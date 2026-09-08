"""Replay existing trusted GPT GenModel files; never compile or admit a proof.

Invoke with explicit --receipt --config --snapshot --batch-witness --tensors
--code (directory containing gencode*.py) --out. Parent launches one bounded
all-device torchrun; --validate-only independently checks durable rank artifacts.
Only PP1/MB1 uniform ordered SUM batches are admitted by the CPU authority.
"""
import argparse
import ast
from copy import deepcopy
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import types

INPUT_NAMES = ('input_ids', 'position_ids')
GRAD_RTOL, GRAD_ATOL = 2e-4, 2e-4
OUTPUT_RTOL, OUTPUT_ATOL = 2e-5, 2e-4


def expected_observation(record, rank):
    if type(rank) is not int:
        raise ValueError('rank must be an integer')
    rows = [x for x in record['rank_inputs'] if x['rank'] == rank]
    if len(rows) != 1:
        raise ValueError('missing/duplicate rank')
    row = deepcopy(rows[0])
    groups = [g for g in record['groups'] if rank in g['ranks']]
    if len(groups) != 1 or row['unit'] != groups[0]['unit']:
        raise ValueError('wrong unit/rank')
    row.update(positions=deepcopy(groups[0]['positions']),
               inputs=deepcopy(groups[0]['inputs']), tuple_names=list(INPUT_NAMES),
               dtypes=['torch.int64'] * len(INPUT_NAMES))
    return row


def validate_observations(observations, record, rank):
    if observations != [expected_observation(record, rank)]:
        raise ValueError('consumed tuple/unit/rank/ref/position/value mismatch')


class ObservedIterator:
    """Inserted immediately at the real generated schedule's next boundary."""
    def __init__(self, iterator, record, rank):
        self.iterator = iter(iterator)
        self.record, self.rank = record, rank
        self.observations, self.tensors = [], []

    def __iter__(self):
        return self

    def __next__(self):
        values = next(self.iterator)
        if not isinstance(values, tuple) or len(values) != len(INPUT_NAMES):
            raise ValueError('generated input must be the exact ordered tensor tuple')
        row = expected_observation(self.record, self.rank)
        copies = tuple(v.detach().cpu().clone() for v in values)
        row['inputs'] = {k: v.tolist() for k, v in zip(INPUT_NAMES, copies, strict=True)}
        row['dtypes'] = [str(v.dtype) for v in copies]
        self.observations.append(row)
        self.tensors.append(copies)
        validate_observations(self.observations, self.record, self.rank)
        return values


def validate_rank_domain(rows, world):
    ranks = [r['rank'] for r in rows]
    if (any(type(r) is not int for r in ranks) or len(ranks) != world or
            set(ranks) != set(range(world))):
        raise ValueError('missing/extra/duplicate/wrong rank domain')


def metadata_map(fullmap):
    return {n: dict(orig_name=m.orig_name, shape=list(m.shape),
                   slicers=[[s.start, s.stop, s.step] for s in m.slicers],
                   val_chunks=m.val_chunks) for n, m in fullmap.items()}


def shard(source, meta, gradient=False):
    if list(source.shape) != meta['shape']:
        raise ValueError('source full shape mismatch')
    if type(meta['val_chunks']) is not int or meta['val_chunks'] < 1:
        raise ValueError('invalid value partition')
    # Native load_attr_content divides PARAMETER values by val_chunks.
    # The gradient correspondence for value-partitioned parameters needs a
    # separate authority; reject rather than guessing its chain-rule factor.
    if gradient and meta['val_chunks'] != 1:
        raise ValueError('unsupported source: value-partition gradient contract')
    result = source[tuple(slice(*s) for s in meta['slicers'])]
    return result if meta['val_chunks'] == 1 else result / meta['val_chunks']


def exact(a, b):
    import torch
    if a.shape != b.shape or a.dtype != b.dtype or not torch.equal(a.cpu(), b.cpu()):
        raise ValueError('exact tensor shape/dtype/value mismatch')


def require_finite_output(value):
    import torch
    if not torch.isfinite(value).all():
        raise ValueError('nonfinite generated/reference output')


def check_output(actual, expected):
    import torch
    require_finite_output(actual)
    require_finite_output(expected)
    torch.testing.assert_close(actual, expected, rtol=OUTPUT_RTOL, atol=OUTPUT_ATOL)


def check_shards(actual, expected_meta, state, global_grads):
    import torch
    if actual['metadata'] != expected_meta:
        raise ValueError('actual fullmap differs from generated artifact metadata')
    names = set(expected_meta)
    if set(actual['initialized']) != names or set(actual['grads']) != names:
        raise ValueError('missing/extra named parameter shards')
    errors = {}
    for name, meta in expected_meta.items():
        exact(actual['initialized'][name], shard(state[meta['orig_name']], meta))
        expected = shard(global_grads[meta['orig_name']], meta, gradient=True)
        if not torch.isfinite(actual['grads'][name]).all() or not torch.isfinite(expected).all():
            raise ValueError('nonfinite global/local gradient')
        torch.testing.assert_close(actual['grads'][name], expected,
                                   rtol=GRAD_RTOL, atol=GRAD_ATOL)
        errors[name] = (actual['grads'][name]-expected).abs().max().item()
    return errors


def read(path):
    return json.loads(Path(path).read_text())


def save_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')


def load_inputs(args):
    import torch
    from trainverify.batch_source_authority import validate_batch_record
    receipt, config, snapshot, witness = map(read, (args.receipt, args.config,
                                                  args.snapshot, args.batch_witness))
    record = witness['batch']
    if config != record['config'] or receipt != witness['capture_receipt']:
        raise ValueError('explicit config/receipt differs from saved batch witness')
    validate_batch_record(record, snapshot, receipt, witness['reference_capture_receipt'])
    tensors = torch.load(args.tensors, weights_only=True, map_location='cpu')
    if len(tensors['unit_inputs']) != len(record['groups']):
        raise ValueError('saved unit tensor domain')
    for inputs, expected in [(tensors['global_inputs'], record['global_inputs'])] + [
            (v, g['inputs']) for v, g in zip(tensors['unit_inputs'], record['groups'], strict=True)]:
        if set(inputs) != set(INPUT_NAMES):
            raise ValueError('saved input name domain')
        for name in INPUT_NAMES:
            exact(inputs[name], torch.tensor(expected[name], dtype=torch.int64))
    return receipt, record, snapshot, tensors


def validate_generated_source(actual, captured):
    if ast.dump(ast.parse(actual)) != ast.dump(ast.parse(captured)):
        raise ValueError('full generated source differs from typed snapshot')


def load_generated(args, rank, record, snapshot):
    path = args.code / f'gencode{rank}.py'
    validate_generated_source(path.read_text(), snapshot['rank_sources'][str(rank)])
    tree = ast.parse(path.read_text())
    schedule = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == '_train_step')
    captured = next(n for n in ast.parse(snapshot['rank_sources'][str(rank)]).body
                    if isinstance(n, ast.FunctionDef) and n.name == '_train_step')
    if ast.dump(schedule) != ast.dump(captured):
        raise ValueError('generated schedule differs from typed snapshot')
    binding = expected_observation(record, rank)
    targets = [n.targets[0] for n in ast.walk(schedule) if isinstance(n, ast.Assign)
               and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Name)
               and n.value.func.id == 'next']
    expected = [f"{name}_{ref['source_tid']}" for name, ref in zip(INPUT_NAMES, binding['refs'], strict=True)]
    if len(targets) != 1 or not isinstance(targets[0], ast.Tuple) or [n.id for n in targets[0].elts] != expected:
        raise ValueError('generated next tuple source order mismatch')
    name = f'_batch_runtime_rank_{rank}'
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    module.GenModel.runtime_version = module.runtime_version
    return module


def canonical(receipt, tensors, device):
    import torch
    from genmodel.model.gpt import Config, GPT
    model = GPT(Config(**receipt['model'])).to(device=device, dtype=torch.float32)
    state = {n: t.to(dtype=torch.float32, device=device) if t.is_floating_point()
             else t.to(device) for n, t in tensors['initial_state'].items()}
    if set(state) != set(model.state_dict()):
        raise ValueError('full canonical state name coverage')
    for name, value in model.state_dict().items():
        if value.shape != state[name].shape or value.dtype != state[name].dtype:
            raise ValueError('canonical full state shape/dtype')
    model.load_state_dict(state, strict=True)
    for name, value in model.state_dict().items():
        exact(value, state[name])
    return model, {n:t.cpu() for n,t in state.items()}


def worker(args):
    import torch
    import torch.distributed as dist
    receipt, record, snapshot, tensors = load_inputs(args)
    rank, local = int(os.environ['RANK']), int(os.environ['LOCAL_RANK'])
    torch.cuda.set_device(local)
    # Supported pre-initialized process-group path avoids newer init API kwargs.
    dist.init_process_group('nccl')
    if dist.get_world_size() != receipt['compute']['runtime_ngpus']:
        raise ValueError('runtime world mismatch')
    torch.set_num_threads(1)
    module = load_generated(args, rank, record, snapshot)
    parallel = module.GenModel(init_params=False, build_buckets=False).cuda()
    model, state = canonical(receipt, tensors, 'cuda')
    fullmap = parallel.fullmap
    attrs = dict(parallel.named_parameters()) | dict(parallel.named_buffers())
    if set(attrs) != set(fullmap):
        raise ValueError('actual fullmap does not cover full state')
    with torch.no_grad():
        for name, part in attrs.items():
            expected = shard(state[fullmap[name].orig_name], metadata_map(fullmap)[name])
            if part.shape != expected.shape or part.dtype != expected.dtype:
                raise ValueError('generated initial shard shape/dtype mismatch')
            part.copy_(expected)
            exact(part, expected)
    parallel.build_buckets()
    meta = metadata_map({n:fullmap[n] for n,_ in parallel.named_parameters()})
    initialized = {n:p.detach().cpu().clone() for n,p in parallel.named_parameters()}
    unit = expected_observation(record, rank)['unit']
    inputs = tuple(tensors['unit_inputs'][unit][k].cuda() for k in INPUT_NAMES)
    with torch.no_grad():
        unit_output = model(*inputs).detach().cpu()
    if rank == 0:
        global_inputs = {k:v.cuda() for k,v in tensors['global_inputs'].items()}
        global_output = model(**global_inputs)
        require_finite_output(global_output)
        global_output.backward()
        global_grads = {n:p.grad.detach().cpu().clone() for n,p in model.named_parameters()}
        torch.save(dict(grads=global_grads, output=global_output.detach().cpu(),
                        inputs=tensors['global_inputs'], state=state), args.out/'reference.pt')
    dist.barrier()
    reference = torch.load(args.out/'reference.pt', weights_only=True)
    observers = []
    def observed_step(self, dataloader):
        observed = ObservedIterator(dataloader, record, rank)
        observers.append(observed)
        return module._train_step(self, observed)
    parallel._train_step = types.MethodType(observed_step, parallel)
    outputs = parallel.train_step([inputs])
    observations = [x for ob in observers for x in ob.observations]
    validate_observations(observations, record, rank)
    actual = dict(rank=rank, observations=observations, metadata=meta,
        initialized=initialized,
        grads={n:p.grad.detach().cpu().clone() for n,p in parallel.named_parameters()},
        inputs=[v for ob in observers for v in ob.tensors],
        output=outputs[0].detach().cpu(), unit_output=unit_output)
    # Preserve failed numerical evidence too, before assertions.
    torch.save(actual, args.out/f'rank{rank}.pt')
    errors = check_shards(actual, meta, state, reference['grads'])
    check_output(actual['output'], unit_output)
    save_json(args.out/f'rank{rank}.json', dict(rank=rank, inner_exit=0,
        source_binding=observations, parameter_names=list(meta), gradient_errors=errors,
        output=actual['output'].item(), unit_reference=unit_output.item(),
        numerical_runtime_checked=False, historicalcapture_sample_association=False,
        new_run_consumed_payload_association=True, kernel_value_proved=False,
        proof_admissible=False))
    dist.barrier()
    dist.destroy_process_group()


def aggregate(args):
    import torch
    receipt, record, snapshot, tensors = load_inputs(args)
    world = receipt['compute']['runtime_ngpus']
    paths = sorted(args.out.glob('rank*.json'))
    rows = [read(p) for p in paths]
    validate_rank_domain(rows, world)
    if {p.name for p in args.out.glob('rank*.pt')} != {f'rank{r}.pt' for r in range(world)}:
        raise ValueError('rank tensor artifact domain')
    model, state = canonical(receipt, tensors, 'cpu')
    names = set(dict(model.named_parameters()))
    reference = torch.load(args.out/'reference.pt', weights_only=True)
    require_finite_output(reference['output'])
    if set(reference['grads']) != names or set(reference['state']) != set(state):
        raise ValueError('global reference full parameter name coverage')
    for name in state:
        exact(reference['state'][name], state[name])
    for name in INPUT_NAMES:
        exact(reference['inputs'][name], tensors['global_inputs'][name])
    checked, max_error = 0, 0.
    reconstructed = {k:[None]*record['config']['gbs'] for k in INPUT_NAMES}
    for row in rows:
        rank = row['rank']
        if row['inner_exit'] != 0:
            raise ValueError('rank failed')
        actual = torch.load(args.out/f'rank{rank}.pt', weights_only=True)
        if actual['rank'] != rank:
            raise ValueError('rank artifact identity')
        validate_observations(actual['observations'], record, rank)
        if row['source_binding'] != actual['observations'] or len(actual['inputs']) != 1:
            raise ValueError('rank JSON/tensor source binding mismatch')
        expected = expected_observation(record, rank)
        for name, value in zip(INPUT_NAMES, actual['inputs'][0], strict=True):
            exact(value, torch.tensor(expected['inputs'][name], dtype=torch.int64))
            for local, pos in enumerate(expected['positions']):
                previous = reconstructed[name][pos]
                if previous is not None and previous != value[local].tolist():
                    raise ValueError('replication group input disagreement')
                reconstructed[name][pos] = value[local].tolist()
        module = load_generated(args, rank, record, snapshot)
        meta = metadata_map({n:m for n,m in module.GenModel.attr_meta_maps[rank].items() if m.is_param})
        if {m['orig_name'] for m in meta.values()} != names or set(row['parameter_names']) != set(meta):
            raise ValueError('actual model full parameter name coverage')
        errors = check_shards(actual, meta, state, reference['grads'])
        check_output(actual['output'], actual['unit_output'])
        checked += len(errors)
        max_error = max(max_error, max(errors.values()))
    if reconstructed != record['global_inputs']:
        raise ValueError('logical global sample partition reconstruction mismatch')
    result = dict(numerical_runtime_checked=True, ranks_checked=world,
        parameter_shards_checked=checked, global_parameter_names=sorted(names),
        max_gradient_abs_error=max_error, logical_sample_partition=record['samples'],
        reconstructed_global_inputs=reconstructed, new_run_consumed_payload_association=True,
        historicalcapture_sample_association=False, kernel_value_proved=False,
        proof_admissible=False, gradient_rtol=GRAD_RTOL, gradient_atol=GRAD_ATOL,
        output_rtol=OUTPUT_RTOL, output_atol=OUTPUT_ATOL,
        reference='one canonical CUDA FP32 concatenated global batch; no normalization')
    save_json(args.out/'result.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('receipt','config','snapshot','batch-witness','tensors','code','out'):
        parser.add_argument('--'+name, type=Path, required=True)
    parser.add_argument('--worker', action='store_true')
    parser.add_argument('--validate-only', action='store_true')
    args = parser.parse_args()
    if args.worker:
        worker(args)
        return
    if args.validate_only:
        print(json.dumps(aggregate(args)))
        return
    receipt, _, _, _ = load_inputs(args)
    args.out.mkdir(parents=True, exist_ok=False)
    world = receipt['compute']['runtime_ngpus']
    gpu = subprocess.run(['nvidia-smi'], capture_output=True, text=True, check=True)
    busy = subprocess.run(['nvidia-smi','--query-compute-apps=pid','--format=csv,noheader'],
                          capture_output=True, text=True, check=True)
    ps = subprocess.run(['ps','-eo','pid,args'], capture_output=True, text=True, check=True)
    save_json(args.out/'preflight.json', dict(nvidia_smi=gpu.stdout, gpu_processes=busy.stdout, processes=ps.stdout))
    if busy.stdout.strip() or any('torch.distributed.run' in line or '/bin/torchrun ' in line
                                for line in ps.stdout.splitlines()):
        raise RuntimeError('GPU/distributed process busy; refusing launch')
    import torch
    if torch.cuda.device_count() != world:
        raise ValueError('requires all visible GPUs matching receipt runtime world')
    argv = [sys.executable,'-m','torch.distributed.run','--standalone',f'--nproc_per_node={world}',
            '-m','scripts.gpt_batch_runtime']
    for name in ('receipt','config','snapshot','batch_witness','tensors','code','out'):
        argv += ['--'+name.replace('_','-'), str(getattr(args,name).resolve())]
    argv += ['--worker']
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', OMP_NUM_THREADS='1',
               TMPDIR=str(args.out.resolve()), XDG_CACHE_HOME=str(args.out.resolve()/'cache'),
               TORCH_HOME=str(args.out.resolve()/'torch'), TRITON_CACHE_DIR=str(args.out.resolve()/'triton'))
    with (args.out/'torchrun.log').open('w') as log:
        proc = subprocess.Popen(argv, stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True)
        launch = dict(command=argv, pid=proc.pid, process_group=proc.pid, timeout_seconds=240,
                      log=str(args.out/'torchrun.log'), inner_exit=None,
                      environment={k:env.get(k) for k in ('CUDA_VISIBLE_DEVICES','PYTHONDONTWRITEBYTECODE',
                          'OMP_NUM_THREADS','TMPDIR','XDG_CACHE_HOME','TORCH_HOME','TRITON_CACHE_DIR')})
        save_json(args.out/'launch.json', launch)
        try:
            launch['inner_exit'] = proc.wait(timeout=240)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
            launch['inner_exit'] = 124
        finally:
            # Kill any owned descendants even when torchrun exits before them.
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()
            save_json(args.out/'launch.json', launch)
    if launch['inner_exit'] != 0:
        save_json(args.out/'result.json', dict(numerical_runtime_checked=False,
            proof_admissible=False, kernel_value_proved=False,
            historicalcapture_sample_association=False, error='actual GPU runtime failure; see torchrun.log'))
        raise SystemExit(launch['inner_exit'])
    print(json.dumps(aggregate(args)))


if __name__ == '__main__':
    main()
