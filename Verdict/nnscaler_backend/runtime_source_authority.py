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


def export_expanded_cells(world, cells):
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
        for ir in (*cell._input_irs, *cell._output_irs):
            if ir.is_attr():
                placements[(node.wtype, node.rank, ir.tid)] = dict(
                    parent_tid=ir.parent.tid, name=ir.parent.name,
                    full_shape=list(ir.parent.shape), indmap=[list(p) for p in ir.indmap],
                    valmap=list(ir.valmap), is_attr=ir.is_attr(), is_grad=ir.is_grad(),
                    scale_unit=node.rank // world.plan_ndevs,
                    plan_rank=node.rank % world.plan_ndevs)
    snapshot = build_snapshot(writers)
    for tensor in snapshot["tensors"]:
        ref = tensor["ref"]
        key = (ref["world"], ref["runtime_rank"], ref["source_tid"])
        if key in placements:
            tensor["placement"] = placements[key]
    return snapshot


def load_capture(capture_path, world_path=None, wtype="p"):
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
    cells, _ = _fuse_collective_inputs(cells)
    snapshot = export_expanded_cells(world, cells)
    snapshot["source"] = dict(capture=str(capture_path), world_sidecar=str(world_path),
                              plan_ndevs=world.plan_ndevs, runtime_ndevs=world.runtime_ndevs,
                              dataflow_order="expanded-cell-order; fused-inputs-indmap-order",
                              call_instance="zero-based expanded occurrence per world/rank/mb/cid/origin")
    validate_snapshot(snapshot)
    return snapshot
