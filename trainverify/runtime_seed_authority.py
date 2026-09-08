"""External autograd seed evidence, deliberately NOT a proof authority.

Source requests and live measurements are separate. A scalar [] observation has
representational intent [1], valAt0=1; no mathematical embedding is established.
No Graph nodes, initial-state assumptions, or kernel admissions are produced.
"""
from copy import deepcopy


def bind_seed_inventory(writers, paths):
    """Recompute full writer/consumer inventory, never trust seed metadata.

    This low-level consistency check does NOT authenticate supplied dictionaries.
    capture_seed_requests obtains both streams from the original trusted IR.
    """
    from .runtime_source_authority import build_snapshot, tensor_export_id, writer_export_id
    snapshot = build_snapshot(writers)
    written = {t['export_id'] for t in snapshot['tensors'] if t['writer'] is not None}
    consumers = [w for w in writers if w['ref']['op'] == 'BW_sum']
    if len(consumers) != len(paths) or not consumers:
        raise ValueError('missing/duplicate seed inventory')
    seen = set()
    for writer, path in zip(consumers, paths):
        seed = tensor_export_id(path['seed'])
        tensor_export_id(path['x'])
        if seed in seen or seed in written:
            raise ValueError('duplicate seed or raw writer exists')
        seen.add(seed)
        if (writer_export_id(path['bw_writer']) != writer_export_id(writer['ref'])
                or writer['inputs'] != [path['seed'], path['x']]
                or len(writer['outputs']) != 1):
            raise ValueError('BW input/fullref/version/order mismatch')
    return deepcopy(paths)


def capture_seed_requests(mg, world, rank_sources):
    """Rebuild from a trusted original ModuleCodeGen, never serialized seed claims.

    Whole raw graph inventory, original prepared sum/mirror gradient ports, and
    original scaled execution plan are independently joined. No pickle loading
    or source execution is performed here. The caller owns trusted artifact
    loading; rank_sources must be the original generated files for that capture.
    This is deliberately bounded to PP1/MB1 full torch.sum and an optional
    AllReduceIdentity forward tail. Static source agreement is not hook absence.
    """
    import ast
    import inspect
    import textwrap
    from nnscaler.codegen.module.module import ModuleCodeGen
    from nnscaler.codegen.emit import CodeEmission
    from nnscaler.graph.segment import IRSegment
    from nnscaler_backend.build_graph import _prepare_rank_cells, _flatten_exereuse_then_scale, _fuse_collective_inputs
    from nnscaler_backend.runtime_source_authority import capture_adapter_source, export_expanded_cells
    from nnscaler.runtime.executor import Executor
    from nnscaler.runtime.adapter.nn import AllReduceIdentity
    import torch

    def require(ok, reason):
        if not ok:
            raise ValueError(reason)

    require(isinstance(mg, ModuleCodeGen), 'requires original ModuleCodeGen')
    require(world.num_pp == 1 and world.num_mb == 1, 'unsupported PP/MB domain')
    require(set(rank_sources) == set(range(world.runtime_ndevs)), 'full generated rank inventory required')
    cells = [c for rank in range(world.runtime_ndevs) for c in _prepare_rank_cells(world, mg, rank)]
    prepared = capture_adapter_source(cells)
    # The canonical fused raw graph, not just prefix ranks or the metadata table.
    raw_cells, _ = _fuse_collective_inputs(cells)
    raw = export_expanded_cells(world, raw_cells)
    emit = CodeEmission()
    paths = []
    for bw, row in zip(cells, prepared):
        if bw.opname.name != 'BW_sum':
            continue
        require(bw.node.mb == 0, 'unsupported repeated backward microbatch')
        fw_ir = bw.ir.mirror
        fws = [(c, r) for c, r in zip(cells, prepared)
               if c.rank == bw.rank and c.opname.name == 'FW_sum' and c.ir.cid == fw_ir.cid]
        require(len(fws) == 1, 'missing/duplicate sum mirror')
        fw, fwrow = fws[0]
        require(fw.ir.mirror.cid == bw.ir.cid and fw.ir.signature == 'torch.sum', 'sum mirror/signature mismatch')
        require(len(fw.ir.inputs()) == len(fw.ir.outputs()) == len(bw.ir.inputs()) == 1,
                'unsupported sum port arity')
        require(not fwrow['generated_producer']['kwargs'], 'unsupported non-full sum')
        seed = row['inputs'][0]
        require(fw.ir.output(0).grad is not None and fw.ir.output(0).grad.tid == bw.ir.input(0).tid == seed['source_tid'],
                'None/gradient mirror identity mismatch')
        require(row['inputs'][1:] == fwrow['inputs'] and seed['version'] == 0,
                'sum primal/seed raw version mismatch')
        seq = _flatten_exereuse_then_scale(mg.execplan.seq(bw.rank % world.plan_ndevs), mg, bw.rank)
        segments = [(i, s) for i, s in enumerate(seq) if isinstance(s, IRSegment) and s.isfw()
                    and any(n.cid == fw.ir.cid for n in s.nodes())]
        require(len(segments) == 1, 'ambiguous forward segment')
        index, segment = segments[0]
        require(index + 1 < len(seq) and isinstance(seq[index+1], IRSegment)
                and not seq[index+1].isfw() and seq[index+1].mirror.cid == segment.cid,
                'backward execution plan order/target mismatch')
        back = seq[index+1]
        require(len(segment.outputs()) == len(back.inputs()) == 1 and not back.outputs()
                and any(n.cid == bw.ir.cid for n in back.nodes()), 'unsupported backward segment ports')
        output_ir = segment.output(0)
        require(output_ir.grad is not None and output_ir.grad.tid == back.input(0).tid == seed['source_tid'],
                'segment output gradient differs from sum external seed')
        method = 'segment' + str(segment.cid)
        tree = ast.parse(rank_sources[bw.rank])
        cls, = [n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'GenModel']
        fn, = [n for n in cls.body if isinstance(n, ast.FunctionDef) and n.name == method]
        train, = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == '_train_step']
        sum_name, x_name = emit.tensor_name(fw.ir.output(0)), emit.tensor_name(fw.ir.input(0))
        out_name = emit.tensor_name(output_ir)
        sum_sites = [s for s in fn.body if isinstance(s, ast.Assign) and len(s.targets) == 1
                     and ast.unparse(s.targets[0]) == sum_name]
        require(len(sum_sites) == 1 and ast.unparse(sum_sites[0].value) == f'torch.sum({x_name})',
                'generated full sum output/input identity mismatch')
        tail = fn.body[fn.body.index(sum_sites[0])+1:]
        useful = [s for s in tail if not isinstance(s, ast.Delete)]
        identity = sum_name != out_name
        expected_tail = f'return {out_name}'
        ranks = None
        if identity:
            adapters = [(c,r) for c,r in zip(cells,prepared) if c.rank == bw.rank
                        and r.get('primitive',{}).get('kind') == 'AllReduceIdentityPrim'
                        and r['inputs'] == fwrow['outputs']]
            require(len(adapters) == 1, 'missing/duplicate AllReduceIdentity source path')
            adapter, ar = adapters[0]
            require(ar['primitive']['forward'] is True and len(ar['outputs']) == 1
                    and ar['outputs'][0]['source_tid'] == output_ir.tid,
                    'identity adapter output mismatch')
            ranks = ar['primitive']['kwargs']['ranks']
            expected_tail = (f'{out_name} = nnscaler.runtime.adapter.nn.allreduce_identity({sum_name}, ranks={ranks!r})\n'
                             + expected_tail)
        require(ast.dump(ast.Module(body=useful, type_ignores=[])) == ast.dump(ast.parse(expected_tail)),
                'unsupported generated sum-to-output tail')
        backwards = [s for s in train.body if isinstance(s, ast.Assign) and isinstance(s.value, ast.Call)
                     and ast.unparse(s.value.func) == 'nnscaler.runtime.executor.backward']
        require(len(backwards) == 1, 'missing/duplicate generated backward schedule')
        call = backwards[0].value
        expected_call = ast.parse(f"nnscaler.runtime.executor.backward({method!r}, (), ({out_name},), (None,))", mode='eval').body
        require(ast.dump(call) == ast.dump(expected_call), 'generated None/backward target/output mismatch')
        forwards = [s for s in train.body if isinstance(s, ast.Assign) and isinstance(s.value, ast.Call)
                    and ast.unparse(s.value.func) == 'nnscaler.runtime.executor.fexecute']
        require(len(forwards) == 1 and len(forwards[0].targets) == 1
                and ast.unparse(forwards[0].targets[0]) == out_name,
                'unsupported generated forward schedule')
        fcall = forwards[0].value
        require(len(fcall.args) >= 2 and ast.literal_eval(fcall.args[0]) == method
                and ast.unparse(fcall.args[1]) == 'model.' + method
                and len(fcall.keywords) == 1 and fcall.keywords[0].arg == 'requires_grad'
                and ast.literal_eval(fcall.keywords[0].value) is True,
                'generated differentiable forward target mismatch')
        fi, bi = train.body.index(forwards[0]), train.body.index(backwards[0])
        require(fi < bi and all(isinstance(s, ast.Delete) for s in train.body[fi+1:bi]),
                'intervening generated backward output writer/callback')
        require(sum(1 for n in ast.walk(train) if isinstance(n, ast.Call)
                    and ast.unparse(n.func) == 'nnscaler.runtime.executor.backward') == 1,
                'hidden backward schedule call')
        paths.append(dict(seed=seed, bw_writer=row['ref'], x=row['inputs'][1],
                          fw_writer=fwrow['ref'], sum_output=fwrow['outputs'][0],
                          output_name=out_name, sum_name=sum_name, segment=method,
                          backward_cid=back.cid, schedule_ordinal=index+1,
                          generated_backward_line=call.lineno, generated_sum_line=sum_sites[0].lineno,
                          identity_backward=identity, ranks=ranks,
                          denote_intent=dict(shape=[1], valAt0=1)))
    paths = bind_seed_inventory(raw['writers'], paths)
    runtime_sources = {name: textwrap.dedent(inspect.getsource(fn)) for name,fn in (
        ('Executor.backward',Executor.backward), ('torch.autograd._make_grads',torch.autograd._make_grads),
        ('AllReduceIdentity.backward',AllReduceIdentity.backward))}
    return dict(format='trainverify.external-seed-source.v1', scope='source-only',
                source_path_validated=True, runtime_accepted=False,
                proof_admissible=False, kernel_value_proved=False,
                raw_writer_count=len(raw['writers']), raw_tensor_count=len(raw['tensors']),
                requests=paths, runtime_sources=runtime_sources)


class ScalarSeedObserver:
    """Read-only observations around a single normal backward invocation.

    _make_grads receives original arguments once. Dispatch observes the scalar
    input to aten.expand inside the exact SumBackward0, after node prehooks.
    No hook is removed or gradient substituted. This is controlled, serial
    Python instrumentation, not a concurrent adversarial sandbox. Source/run
    association is a separate gate; posthook/operator refinement is not proved.
    """
    def __init__(self, executor, output, sum_output, run_id):
        self.executor, self.output, self.sum_output = executor, output, sum_output
        self.run_id = run_id
        self._receipt = None
        self.used = False

    def run(self, backward):
        import torch
        self._receipt = None
        if self.used:
            raise ValueError('stale observer cannot be reused')
        self.used = True
        if not isinstance(self.run_id, str) or not self.run_id:
            raise ValueError('missing fresh run identity')
        def live_state():
            if getattr(self.executor, '_backward_pre_hook', object()) is not None:
                raise ValueError('unsupported live executor prehook')
            for tensor in (self.output, self.sum_output):
                if (type(tensor) is not torch.Tensor or tensor.shape != torch.Size([])
                        or not tensor.requires_grad or not tensor.is_floating_point()
                        or tensor.grad_fn is None):
                    raise ValueError('requires real differentiable scalar [] output')
                if tensor._backward_hooks or tensor._post_accumulate_grad_hooks:
                    raise ValueError('unsupported live tensor hook')
        live_state()
        original = torch.autograd._make_grads
        observed, arrived = [], []
        attempts = 0

        def make_grads(outputs, grads, is_grads_batched):
            nonlocal attempts
            attempts += 1
            live_state()
            if (len(outputs) != 1 or outputs[0] is not self.output or len(grads) != 1
                    or grads[0] is not None or is_grads_batched is not False):
                raise ValueError('None/output identity mismatch or unsupported gradient arguments')
            if observed:
                raise ValueError('duplicate seed event')
            result = original(outputs, grads, is_grads_batched)
            observed.append(result[0].detach().cpu().clone())
            return result

        from torch.utils._python_dispatch import TorchDispatchMode
        node = self.sum_output.grad_fn
        if type(node).__name__ != 'SumBackward0':
            raise ValueError('unsupported sum consumer')
        class Consumer(TorchDispatchMode):
            def __torch_dispatch__(self, func, types, args=(), kwargs=None):
                if torch._C._current_autograd_node() is node and func is torch.ops.aten.expand.default:
                    live_state()
                    arrived.append(args[0].detach().cpu().clone())
                return func(*args, **(kwargs or {}))
        try:
            torch.autograd._make_grads = make_grads
            with Consumer():
                result = backward()
            live_state()
            if torch.autograd._make_grads is not make_grads:
                raise ValueError('observer replaced during backward')
            if attempts != 1 or len(observed) != 1 or len(arrived) != 1:
                raise ValueError('missing/duplicate seed event')
            if any(t.shape != torch.Size([]) or not t.is_floating_point()
                   or t.dtype != self.sum_output.dtype or t.item() != 1 for t in observed + arrived):
                raise ValueError('observed seed is not an exact scalar unit')
            self._observed_tensor, self._effective_tensor = observed[0], arrived[0]
            self._receipt = dict(format='trainverify.external-seed-observation.v1',
                run_id=self.run_id, unit_seed_observed=True,
                observed_seed=dict(torch_shape=[], value=observed[0].item()),
                effective_seed=dict(torch_shape=[], value=arrived[0].item(), dtype=str(arrived[0].dtype)),
                consumer='SumBackward0/aten.expand.default',
                denote_intent=dict(shape=[1], valAt0=1),
                runtime_accepted=False, proof_admissible=False, kernel_value_proved=False,
                missing=['source-to-live-output/schedule association',
                         'independent fresh manifest/event/PT binding',
                         'kernel scalar representation adapter'])
            return result
        finally:
            torch.autograd._make_grads = original

    def receipt(self):
        if self._receipt is None:
            raise ValueError('no valid seed observation')
        return deepcopy(self._receipt)


def validate_seed_event(authority, event, actual, manifest, rank):
    """Rebind event/PT to independently rebuilt original requests and run file.

    This is an association check, not authentication of arbitrary dictionaries.
    The caller must rebuild authority from its explicit trusted capture and read
    the independent manifest, never either path from the event under test.
    """
    import torch
    from .batch_source_authority import _same_handoff_data as same
    try:
        if (type(rank) is not int or type(manifest['world']) is not int
                or not 0 <= rank < manifest['world']
                or manifest['format'] != 'trainverify.input-handoff-run.v1'
                or type(manifest['run_id']) is not str or not manifest['run_id']):
            raise ValueError('invalid independent manifest/rank')
        requests = [q for q in authority['requests'] if q['seed']['runtime_rank'] == rank]
        if len(requests) != 1 or len(authority['requests']) != manifest['world']:
            raise ValueError('missing/duplicate source seed inventory')
        if (not same(event, actual['seed_event']) or not same(event['request'], requests[0])
                or event['run_id'] != manifest['run_id'] or type(event['event_ordinal']) is not int
                or event['event_ordinal'] != 1):
            raise ValueError('event/PT/original request/run mismatch')
        obs = event['observation']
        if (obs['run_id'] != manifest['run_id'] or obs['unit_seed_observed'] is not True
                or obs['runtime_accepted'] is not False or obs['proof_admissible'] is not False
                or obs['kernel_value_proved'] is not False
                or obs['consumer'] != 'SumBackward0/aten.expand.default'):
            raise ValueError('invalid observation scope or consumer')
        tensors = actual['seed_tensors']
        if set(tensors) != {'requested', 'effective'}:
            raise ValueError('seed tensor payload domain')
        for key, field in [('requested', 'observed_seed'), ('effective', 'effective_seed')]:
            value = tensors[key]
            if (type(value) is not torch.Tensor or value.shape != torch.Size([])
                    or not value.is_floating_point() or not torch.isfinite(value).item()
                    or value.item() != 1 or type(obs[field]['value']) is not float
                    or obs[field]['torch_shape'] != [] or obs[field]['value'] != value.item()):
                raise ValueError('invalid exact floating scalar unit/PT metadata')
        if (tensors['requested'].dtype != tensors['effective'].dtype
                or str(tensors['effective'].dtype) != obs['effective_seed']['dtype']):
            raise ValueError('mixed seed dtype')
        return dict(new_run_seed_consumer_association=True, runtime_accepted=False,
                    proof_admissible=False, kernel_value_proved=False)
    except (KeyError, TypeError, AttributeError) as exc:
        raise ValueError(f'malformed seed evidence: {exc}') from exc


def load_seed_capture(root, world_type='p'):
    """Explicit trusted local capture only; never load a path named by an event."""
    import ast
    import hashlib
    import json
    import pickle
    from pathlib import Path
    from verdict.graph import World, WType
    root = Path(root)
    mg = pickle.loads((root/'capture.pkl').read_bytes())
    world = World(wtype=WType(world_type), plan_ndevs=len(mg.devices),
                  runtime_ndevs=mg.runtime_ndevs, **json.loads((root/'capture.json').read_text()))
    code = root/'code/_parallel_modules/genmodel/model/gpt/GPT/_'
    sources = {rank: (code/f'gencode{rank}.py').read_text() for rank in range(world.runtime_ndevs)}
    # Preparation/fusion can mutate IR; keep pristine codegen for independent regeneration.
    authority = capture_seed_requests(deepcopy(mg), world, sources)
    # Original ModuleCodeGen independently emits the complete executed segment.
    def segment(text, name):
        return next(n for n in ast.walk(ast.parse(text)) if isinstance(n, ast.FunctionDef) and n.name == name)
    for request in authority['requests']:
        rank = request['seed']['runtime_rank']
        generated = mg.gen(rank)
        if ast.dump(segment(generated, request['segment'])) != ast.dump(segment(sources[rank], request['segment'])):
            raise ValueError('original ModuleCodeGen segment differs from runtime source')
    authority['pins'] = {str(path.resolve()): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in [root/'capture.pkl', root/'capture.json', *[code/f'gencode{r}.py' for r in sources]]}
    return authority, sources


class GeneratedSeedObserver:
    """Bind loaded code objects, live segment return, schedule and consumer.

    Source authentication is deliberately supplied separately by original IR
    revalidation, not inferred from a self-reported filename or event hash.
    Uses bounded Python tracing; refuses an already installed trace.
    """
    def __init__(self, model, module, source, request, run_id):
        import types
        self.model, self.module = model, module
        self.request, self.run_id = deepcopy(request), run_id
        self.method = getattr(model, request['segment'])
        self.train = module._train_step
        if (not isinstance(self.method, types.MethodType) or self.method.__self__ is not model
                or self.method.__func__ is not module.GenModel.__dict__[request['segment']]):
            raise ValueError('loaded segment bound identity mismatch')
        compiled = compile(source, self.train.__code__.co_filename, 'exec')
        def codes(code):
            yield code
            for child in code.co_consts:
                if isinstance(child, types.CodeType):
                    yield from codes(child)
        for actual in (self.method.__func__, self.train):
            matches = [c for c in codes(compiled) if c.co_qualname == actual.__code__.co_qualname]
            if len(matches) != 1 or matches[0] != actual.__code__ or actual.__globals__ is not module.__dict__:
                raise ValueError('loaded generated code differs from original source')
        self.codes = (self.method.__func__.__code__, self.train.__code__)
        self.used, self._evidence = False, None

    def run(self, training):
        import sys
        import nnscaler.runtime.executor as executor
        self._evidence = None
        if self.used or sys.gettrace() is not None:
            raise ValueError('stale observer or unsupported existing trace')
        self.used = True
        if ((self.method.__func__.__code__, self.train.__code__) != self.codes
                or self.module._train_step is not self.train
                or self.module.GenModel.__dict__[self.request['segment']] is not self.method.__func__):
            raise ValueError('loaded code changed since source validation')
        fw, bw = executor.fexecute, executor.backward
        method_code, train_code = self.codes
        sums, returns, calls, attempts = [], [], [], []
        output = None
        def trace(frame, event, arg):
            if frame.f_code is method_code:
                summed = frame.f_locals.get(self.request['sum_name'])
                if summed is not None and not any(summed is s for s in sums):
                    sums.append(summed)
                if event == 'return': returns.append(arg)
                return trace
            return None
        def forward(*args, **kwargs):
            nonlocal output
            attempts.append('forward')
            if (sys._getframe(1).f_code is not train_code or calls or len(args) < 2
                    or args[0] != self.request['segment'] or kwargs != {'requires_grad': True}):
                raise ValueError('forward schedule/ordinal mismatch')
            # An input-handoff observer may wrap the bound method, but the exact
            # loaded method must still execute once, captured by its code object.
            calls.append('forward')
            output = fw(*args, **kwargs)
            if len(sums) != 1 or len(returns) != 1 or returns[0] is not output:
                raise ValueError('live forward/sum output identity mismatch')
            if not self.request['identity_backward'] and output is not sums[0]:
                raise ValueError('direct sum return differs')
            return output
        def backward(*args, **kwargs):
            attempts.append('backward')
            if (sys._getframe(1).f_code is not train_code or calls != ['forward'] or kwargs
                    or len(args) != 4 or args[0] != self.request['segment']
                    or args[1] != () or type(args[2]) is not tuple or len(args[2]) != 1
                    or args[2][0] is not output or args[3] != (None,)):
                raise ValueError('backward schedule/output/None/cardinality mismatch')
            calls.append('backward')
            observer = ScalarSeedObserver(executor.Executor, output, sums[0], self.run_id)
            result = observer.run(lambda: bw(*args, **kwargs))
            self._evidence = (dict(run_id=self.run_id, event_ordinal=1,
                request=deepcopy(self.request), observation=observer.receipt()),
                dict(requested=observer._observed_tensor, effective=observer._effective_tensor))
            return result
        try:
            executor.fexecute, executor.backward = forward, backward
            sys.settrace(trace)
            result = training()
            if calls != ['forward', 'backward'] or attempts != calls or self._evidence is None:
                raise ValueError('missing/duplicate generated seed schedule')
            return result
        except BaseException:
            self._evidence = None
            raise
        finally:
            sys.settrace(None)
            executor.fexecute, executor.backward = fw, bw

    def evidence(self):
        if self._evidence is None:
            raise ValueError('no valid generated seed evidence')
        return deepcopy(self._evidence)
