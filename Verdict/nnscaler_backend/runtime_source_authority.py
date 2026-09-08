"""Export the existing expanded Cell stream, before transient IRs are discarded.

Order is exactly the supplied stream/edge order. In the capture entry point it
is the existing builder's fused order (indmap sorted), NOT primitive rank order.
This source-only artifact is separate from schema-3 release receipts.
"""
from collections import defaultdict

from trainverify.runtime_source_authority import build_snapshot


def _tensor_ref(tensor):
    return dict(zip(("world", "runtime_rank", "microbatch", "source_tid", "version"),
                    (tensor.wtype, tensor.rank, tensor.mb, tensor.tid, tensor.v)))


def capture_adapter_source(cells, training_sequences=None):
    """Detach the prepared, pre-fusion stream while primitive IR is still live."""
    from copy import deepcopy
    from trainverify.runtime_source_authority import ADAPTER_OPS
    calls, stream = defaultdict(int), []
    for cell in cells:
        n = cell.node
        origin = "expanded" if cell.ir is None else "nnscaler"
        key = (n.wtype, n.rank, n.mb, n.cid, origin)
        ref = dict(world=n.wtype, runtime_rank=n.rank, microbatch=n.mb,
                   source_cid=n.cid, call_instance=calls[key], op=cell.opname.name, origin=origin)
        calls[key] += 1
        row = dict(ref=ref, inputs=[_tensor_ref(t) for t in cell.inputs],
                   outputs=[_tensor_ref(t) for t in cell.outputs])
        # Preserve independent prepared IR naming before fusion/discard. Backward
        # autograd nodes are NOT Python producer calls in the generated forward.
        from nnscaler.ir.operator import IRFwOperation
        if isinstance(cell.ir, IRFwOperation):
            from nnscaler.ir.tensor import IRSubTensor
            def expression(value):
                if isinstance(value, IRSubTensor):
                    # Same identifier spelling as nnscaler.codegen.emit._safe_repr_value.
                    name = value.name.lstrip("*").replace(".", "_")
                    return ("self." if value.is_attr() else "") + f"{name}_{value.tid}"
                if isinstance(value, (tuple, list)):
                    parts = [expression(v) for v in value]
                    return ("[" + ", ".join(parts) + "]" if isinstance(value, list)
                            else "(" + ", ".join(parts) + ("," if len(parts) == 1 else "") + ")")
                if value is None or isinstance(value, (str, bool, int, float)):
                    return repr(value)
                raise ValueError("unsupported producer argument")
            try:
                row["generated_producer"] = dict(
                    signature=cell.ir.signature,
                    inputs=[expression(v) for v in cell.ir.inputs()],
                    outputs=[expression(v) for v in cell.ir.outputs()],
                    # _set_node_kwargs attaches positional constants to this
                    # dict as Verdict metadata; they remain in ir.inputs().
                    kwargs={k: expression(v) for k, v in cell.ir.kwargs.items()
                            if k != "__consts"})
            except ValueError:
                row["generated_producer_missing"] = "unsupported prepared producer argument"
        if ref["op"] in ADAPTER_OPS or ref["op"] == "ChunkPrim":
            from nnscaler.ir.adapter.prim import CollectivePrim
            if not isinstance(cell.ir, CollectivePrim):
                raise ValueError("missing ordered primitive source")
            row["primitive"] = dict(
                kind=type(cell.ir).__name__, signature=cell.ir.signature,
                kwargs={k: deepcopy(cell.ir.kwargs[k]) for k in ("ranks", "dim", "idim", "odim")
                        if k in cell.ir.kwargs},
                forward=cell.adapter is None or cell.adapter.isfw(),
                generated_inputs=[f"{t.name}_{t.tid}" for t in cell.ir.inputs()],
                generated_outputs=[f"{t.name}_{t.tid}" for t in cell.ir.outputs()])
        if ref["op"] == "ChunkPrim":
            import inspect
            import textwrap
            from nnscaler.ir.adapter.prim import ChunkPrim
            from nnscaler.runtime.adapter import chunk
            if type(cell.ir) is not ChunkPrim:
                raise ValueError("missing actual ChunkPrim source")
            row["primitive"]["runtime"] = dict(
                source=textwrap.dedent(inspect.getsource(chunk)),
                source_file=inspect.getsourcefile(chunk), module=chunk.__module__, name=chunk.__name__)
        if cell.adapter is not None and hasattr(cell.adapter, "mirror"):
            adapter = cell.adapter
            mirror = adapter.mirror
            row["adapter_identity"] = dict(cid=adapter.cid, forward=adapter.isfw(),
                mirror_cid=mirror.cid if mirror is not None else None,
                inputs=[t.tid for t in adapter.inputs()], outputs=[t.tid for t in adapter.outputs()],
                input_grads=[t.grad.tid if t.grad is not None else None for t in adapter.inputs()],
                output_grads=[t.grad.tid if t.grad is not None else None for t in adapter.outputs()])
        stream.append(row)
    # Scaling deep-copies cells, so Python object identity is not a mirror key.
    # Match reciprocal IR adapter identities AND the mirrored primal tensor ports.
    for cell, row in zip(cells, stream):
        if row.get("primitive", {}).get("forward") is not False:
            continue
        mirror = getattr(cell.adapter, "mirror", None)
        if mirror is None:
            continue
        candidates = [r for r in stream if r.get("adapter_identity", {}).get("forward") is True
            and r["ref"]["runtime_rank"] == row["ref"]["runtime_rank"]
            and r["ref"]["microbatch"] == row["ref"]["microbatch"]
            and r["adapter_identity"]["cid"] == mirror.cid
            and r["adapter_identity"]["mirror_cid"] == cell.adapter.cid
            and r["adapter_identity"]["inputs"] == [t.tid for t in mirror.inputs()]
            and r["adapter_identity"]["outputs"] == [t.tid for t in mirror.outputs()]]
        if len(candidates) != 1:
            continue
        fw, = candidates
        import ast
        import importlib
        import inspect
        import textwrap
        signature = row["primitive"]["signature"]
        module_name, function_name = signature.rsplit(".", 1)
        module = importlib.import_module(module_name)
        wrapper = getattr(module, function_name)
        wrapper_source = textwrap.dedent(inspect.getsource(wrapper))
        calls = [n for n in ast.walk(ast.parse(wrapper_source)) if isinstance(n, ast.Call)
                 and isinstance(n.func, ast.Attribute) and n.func.attr == "apply"
                 and isinstance(n.func.value, ast.Name)]
        if len(calls) != 1:
            continue
        class_name = calls[0].func.value.id
        cls = wrapper.__globals__.get(class_name)
        if cls is None:
            continue
        row["autograd"] = dict(forward_writer=deepcopy(fw["ref"]),
            forward_inputs=deepcopy(fw["inputs"]), forward_outputs=deepcopy(fw["outputs"]),
            mirror_inputs=[t.tid for t in mirror.inputs()], mirror_outputs=[t.tid for t in mirror.outputs()],
            mirror_input_grads=[t.grad.tid if t.grad is not None else None for t in mirror.inputs()],
            mirror_output_grads=[t.grad.tid if t.grad is not None else None for t in mirror.outputs()],
            runtime=dict(wrapper_source=wrapper_source, class_source=textwrap.dedent(inspect.getsource(cls)),
                         class_name=class_name, source_file=inspect.getsourcefile(cls),
                         backward_global_functions={name: dict(module=fn.__module__, name=fn.__name__,
                             source_file=inspect.getsourcefile(fn))
                             for name in cls.backward.__code__.co_names
                             if inspect.isfunction(fn := cls.backward.__globals__.get(name))}))
    if training_sequences is not None:
        _capture_training_calls(stream, cells, training_sequences)
    return deepcopy(stream)


def _capture_training_calls(stream, cells, sequences):
    """Detach real scaled execution-plan ports before segment flattening is lost.

    Only direct dataloader -> forward segment ports are represented here. This
    is call alignment, not an assertion that executor synchronization is identity.
    """
    from copy import deepcopy
    import inspect
    import textwrap
    from nnscaler.ir.operator import IRDataOperation
    from nnscaler.graph.segment import IRSegment
    from nnscaler.codegen.emit import CodeEmission
    from nnscaler.runtime.executor import Executor
    from nnscaler.runtime.adapter import AsyncCommHandler
    emit = CodeEmission()
    runtime = {name: textwrap.dedent(inspect.getsource(fn)) for name, fn in (
        ("fexecute", Executor.fexecute), ("sync_tensors", Executor.sync_tensors),
        ("wait", AsyncCommHandler().wait))}
    for rank, sequence in sequences.items():
        data = [(cell, row) for cell, row in zip(cells, stream)
                if cell.rank == rank and isinstance(cell.ir, IRDataOperation)]
        occurrences = defaultdict(int)
        current, ordinal = {}, 0
        calls = []
        for ir in sequence:
            occurrence = occurrences[ir.cid]
            occurrences[ir.cid] += 1
            if isinstance(ir, IRDataOperation):
                matches = [(c, r) for c, r in data if c.ir.cid == ir.cid and c.node.mb == occurrence]
                if len(matches) != 1:
                    continue
                cell, row = matches[0]
                names = [emit.tensor_name(t) for t in ir.outputs()]
                row["generated_dataloader"] = dict(loader=emit.tensor_name(ir.input(0)),
                    outputs=names, output_refs=deepcopy(row["outputs"]),
                    writer=deepcopy(row["ref"]), ordinal=occurrence + 1, runtime=deepcopy(runtime))
                for name, ref in zip(names, row["outputs"]):
                    current[name] = deepcopy(ref)
            elif isinstance(ir, IRSegment) and ir.isfw():
                ordinal += 1
                args = [emit.tensor_name(t) for t in ir.inputs() if not t.is_attr()]
                calls.append(dict(method=emit.node_name(ir), source_cid=ir.cid,
                    runtime_rank=rank, microbatch=occurrence, call_instance=occurrence,
                    ordinal=ordinal, arguments=args, parameters=list(args),
                    input_refs=[deepcopy(current.get(name)) for name in args]))
        for _, row in data:
            if "generated_dataloader" in row:
                row["generated_dataloader"]["training_calls"] = deepcopy(calls)


def export_expanded_cells(world, cells, rank_sources=None, reducer_irs=None, adapter_source=None):
    """Snapshot complete prepared Cells without merging any ranks or versions."""
    writers, placements = [], {}
    calls = defaultdict(int)
    seen_nodes = set()
    for cell in cells:
        node = cell.node
        if node in seen_nodes:
            raise ValueError("duplicate writer source node")
        seen_nodes.add(node)
        origin = "expanded" if cell.ir is None else "nnscaler"
        key = (node.wtype, node.rank, node.mb, node.cid, origin)
        ref = dict(world=node.wtype, runtime_rank=node.rank, microbatch=node.mb,
                   source_cid=node.cid, call_instance=calls[key],
                   op=cell.opname.name, origin=origin)
        calls[key] += 1
        writers.append(dict(ref=ref, source_irname=node.irname,
                            inputs=[_tensor_ref(t) for t in cell.inputs],
                            outputs=[_tensor_ref(t) for t in cell.outputs]))
        if ref["op"] in ("MovePrim", "BroadcastPrim"):
            from nnscaler.ir.adapter.prim import MovePrim, BroadcastPrim
            if not isinstance(cell.ir, (MovePrim, BroadcastPrim)):
                raise ValueError("missing primitive transport source")
            src = cell.ir.kwargs["src"]
            destinations = ([cell.ir.kwargs["dst"]] if isinstance(cell.ir, MovePrim)
                            else [r for r in cell.ir.kwargs["ranks"] if r != src])
            writers[-1]["transport"] = dict(src=src, destinations=destinations)
        if rank_sources is not None:
            writers[-1]["parameter_grad_tids"] = [[g, w] for g, w in cell._gid2wid.items()]
            if ref["op"] == "CROSS_DP_WRED":
                from nnscaler.ir.adapter.adapter import IRWeightReducer
                ir = cell.ir if cell.ir is not None else (reducer_irs or {}).get((cell.rank, node.cid))
                if not isinstance(ir, IRWeightReducer):
                    raise ValueError("missing reducer IR")
                writers[-1]["reducer_ir"] = dict(
                    cid=ir.cid, ranks=sorted(ir.device),
                    nreplicas=ir.nreplicas, parameter_tid=cell._wred_wid)
        for ir in (*cell._input_irs, *cell._output_irs):
            if ir.is_attr():
                placements[(node.wtype, node.rank, ir.tid)] = dict(
                    parent_tid=ir.parent.tid, name=ir.parent.name,
                    full_shape=list(ir.parent.shape), indmap=[list(p) for p in ir.indmap],
                    valmap=list(ir.valmap), is_attr=ir.is_attr(), is_grad=ir.is_grad(),
                    is_param=ir.is_param(),
                    scale_unit=node.rank // world.plan_ndevs,
                    plan_rank=node.rank % world.plan_ndevs)
    snapshot = build_snapshot(writers)
    for tensor in snapshot["tensors"]:
        ref = tensor["ref"]
        key = (ref["world"], ref["runtime_rank"], ref["source_tid"])
        if key in placements:
            tensor["placement"] = placements[key]
    if rank_sources is not None:
        from trainverify.runtime_source_authority import bind_reducers
        if (world.num_pp != 1 or world.num_mb != 1 or world.plan_ndevs <= 0
                or world.runtime_ndevs % world.plan_ndevs != 0
                or any(c.node.mb != 0 for c in cells)):
            raise ValueError("not-supported: requires uniform P|R, PP1/MB1")
        snapshot["rank_sources"] = {str(r): text for r, text in rank_sources.items()}
        snapshot["runtime_ndevs"] = world.runtime_ndevs
        bind_reducers(snapshot)
    if adapter_source is not None:
        from copy import deepcopy
        from trainverify.runtime_source_authority import bind_adapters, ADAPTER_OPS
        snapshot["adapter_source"] = deepcopy(adapter_source)
        for writer, cell in zip(snapshot["writers"], cells):
            if writer["ref"]["op"] in ADAPTER_OPS or writer["ref"]["op"] == "ChunkPrim":
                writer["adapter_kwargs"] = {k: deepcopy(cell.kwargs[k])
                    for k in ("ranks", "dim", "idim", "odim") if k in cell.kwargs}
        bind_adapters(snapshot, allow_translation_mismatch=True)
    return snapshot


def load_capture(capture_path, world_path=None, wtype="p", rank_code_directory=None):
    """Load a *trusted* user pickle and run the existing rank-expansion passes.

    Pickle can execute code: this is not an untrusted upload reader. We use the
    loader's World check and the builder's exact preparation/fusion APIs in one
    CPU process, avoiding caches and retaining transient parameter placement IRs.
    No compilation, numerical execution, reducer proof or batch admission occurs.
    """
    import json
    import pickle
    from pathlib import Path
    from verdict.graph import World, WType
    from nnscaler_backend.load_graph import _sanity_check_world
    from nnscaler_backend.build_graph import _prepare_rank_cells, _fuse_collective_inputs
    from trainverify.runtime_source_authority import validate_snapshot

    capture_path = Path(capture_path)
    world_path = Path(world_path) if world_path is not None else capture_path.with_suffix(".json")
    with capture_path.open("rb") as stream:
        mg = pickle.load(stream)
    world = World(wtype=WType(wtype), plan_ndevs=len(mg.devices),
                  runtime_ndevs=mg.runtime_ndevs, **json.loads(world_path.read_text()))
    _sanity_check_world(world)
    cells = [cell for rank in range(world.runtime_ndevs)
             for cell in _prepare_rank_cells(world, mg, rank)]
    from nnscaler_backend.build_graph import _flatten_exereuse_then_scale
    training_sequences = {rank: _flatten_exereuse_then_scale(
        mg.execplan.seq(rank % world.plan_ndevs), mg, rank)
        for rank in range(world.runtime_ndevs)}
    adapter_source = capture_adapter_source(cells, training_sequences=training_sequences)
    cells, _ = _fuse_collective_inputs(cells)
    rank_sources, reducer_irs = None, {}
    if rank_code_directory is not None:
        from nnscaler.ir.adapter.adapter import IRWeightReducer
        from nnscaler_backend.build_graph import _flatten_exereuse_then_scale
        # Per-weight copy(Cell) intentionally loses its transient IR. Recover the
        # same scaled source nodes; never substitute current CompileFlag values.
        for rank in range(world.runtime_ndevs):
            for ir in _flatten_exereuse_then_scale(mg.execplan.seq(rank % world.plan_ndevs), mg, rank):
                if isinstance(ir, IRWeightReducer):
                    reducer_irs[(rank, ir.cid)] = ir
        rank_sources = {r: (Path(rank_code_directory) / f"gencode{r}.py").read_text()
                        for r in range(world.runtime_ndevs)}
    snapshot = export_expanded_cells(world, cells, rank_sources=rank_sources, reducer_irs=reducer_irs,
                                     adapter_source=adapter_source)
    snapshot["source"] = dict(capture=str(capture_path), world_sidecar=str(world_path),
                              rank_code_directory=str(rank_code_directory) if rank_code_directory is not None else None,
                              plan_ndevs=world.plan_ndevs, runtime_ndevs=world.runtime_ndevs,
                              dataflow_order="expanded-cell-order; fused-inputs-indmap-order",
                              call_instance="zero-based expanded occurrence per world/rank/mb/cid/origin")
    validate_snapshot(snapshot)
    return snapshot
