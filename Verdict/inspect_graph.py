"""Inspect compact NNScaler graphs (SM/PM) and lineage metadata.

Run (recommended):
  conda run -n verdict python Verdict/inspect_graph.py

This prints:
- node list (op/inputs/outputs/placements/kwargs)
- tensor metadata (shape/init + lineage-view fields if available)
- inferred lineages using nnscaler_backend.build_lineage.get_ordered_lineages

Goal: help decide whether lineage can be inferred from DAG structure alone.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SM_GRAPH = ROOT / "genmodel" / "mgeners" / "mlp_mgener_dp1_pp1_tp1_nm1_gbs128_dim128_ly1.pkl"
DEFAULT_PM_GRAPH = ROOT / "genmodel" / "mgeners" / "mlp_mgener_dp1_pp1_tp8_nm1_gbs128_dim128_ly1.pkl"


def _world_fields(W: Any) -> Dict[str, Any]:
    if W is None:
        return {}
    out: Dict[str, Any] = {}
    for k in dir(W):
        if k.startswith(("num_", "plan_", "runtime_")):
            try:
                out[k] = getattr(W, k)
            except Exception:
                pass
    return out


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Inspect compact graphs and lineage metadata.")
    p.add_argument("--sm-pkl", default=str(DEFAULT_SM_GRAPH), help="Path to SM graph pickle")
    p.add_argument("--pm-pkl", default=str(DEFAULT_PM_GRAPH), help="Path to PM graph pickle")
    p.add_argument("--max-nodes", type=int, default=50, help="Max nodes to print per graph")
    p.add_argument("--max-tensors", type=int, default=80, help="Max tensor tids to print per graph")
    p.add_argument("--no-lineages", action="store_true", help="Skip lineage inference")
    p.add_argument(
        "--lineages-from-expanded",
        action="store_true",
        help="Infer lineages from expanded per-rank graphs (recommended).",
    )
    p.add_argument(
        "--lineage-full",
        action="store_true",
        help="Use full lineage inference (computes slice_map; may assert on some graphs).",
    )
    p.add_argument(
        "--focus-tid",
        type=int,
        default=None,
        help="If set, focus on this SM tensor id: print its backward slice and its lineage mapping.",
    )
    p.add_argument(
        "--focus-depth",
        type=int,
        default=6,
        help="Backward-slice depth when using --focus-tid.",
    )
    return p.parse_args()


def _build_producer_index(G: Any) -> Dict[int, List[Tuple[int, Any]]]:
    """Map tid -> list of (nodeIndex, node) that produce it."""
    prod: Dict[int, List[Tuple[int, Any]]] = {}
    for i, n in enumerate(G.nodes()):
        for t in G.node_outputs(n):
            prod.setdefault(int(t.tid), []).append((i, n))
    return prod


def _backward_slice(G: Any, root_tid: int, depth: int) -> Tuple[List[int], List[int]]:
    """Return (reachable_tids, reachable_node_indices) in backward slice."""
    prod = _build_producer_index(G)
    seen_tids = {int(root_tid)}
    seen_nodes: set[int] = set()
    frontier = {int(root_tid)}
    for _ in range(max(depth, 0)):
        if not frontier:
            break
        next_frontier: set[int] = set()
        for tid in list(frontier):
            for node_idx, node in prod.get(tid, []):
                if node_idx in seen_nodes:
                    continue
                seen_nodes.add(node_idx)
                for t_in in G.node_inputs(node):
                    t_id = int(t_in.tid)
                    if t_id not in seen_tids:
                        seen_tids.add(t_id)
                        next_frontier.add(t_id)
        frontier = next_frontier
    return sorted(seen_tids), sorted(seen_nodes)


def print_focus(Gs: Any, Gp: Any, focus_tid: int, depth: int) -> None:
    print("\n== focus ==")
    print("focus_tid:", focus_tid, "depth:", depth)
    tids_s, nodes_s = _backward_slice(Gs, focus_tid, depth)
    tids_p, nodes_p = _backward_slice(Gp, focus_tid, depth)
    print("Gs backward-slice tids:", tids_s)
    print("Gs backward-slice node indices:", nodes_s)
    print("Gp backward-slice tids (note: uses compact tids):", tids_p)
    print("Gp backward-slice node indices:", nodes_p)


def load_graphs_from_disk(sm_path: str, pm_path: str):
    # Mirror Verdict/graph_to_lean.py so this script stays standalone.
    import sys

    sys.path.extend([str(ROOT), str(ROOT / "genmodel"), str(ROOT / "Verdict")])

    from verdict.config import Config  # type: ignore
    from verdict.verifier import StageParallelVerifier  # type: ignore
    from nnscaler_backend import nnScalerGraphBackend  # type: ignore
    from z3_backend import z3Backend  # type: ignore
    from analyze_graph import prepare  # type: ignore

    Config.update_from_args([])
    prepare(Config)

    v = StageParallelVerifier(
        Gs_path=str(sm_path),
        Ws_path=None,
        Gp_path=str(pm_path),
        Wp_path=None,
        graph_backend=nnScalerGraphBackend,
        symbolic_backend=z3Backend,
    )
    return v


def load_compact_graphs(v) -> Tuple[Any, Any]:
    return v.get_graph_compact()


def load_expanded_graphs(v) -> Tuple[Any, Any]:
    return v.get_graph()


def _tid_list(ts: Sequence[Any]) -> List[int]:
    return [int(t.tid) for t in ts]


def _fmt_op(op: Any) -> str:
    # nnscaler_backend uses OpName; str() is ok.
    return str(op)


def print_nodes(G: Any, name: str, max_nodes: int) -> None:
    nodes = list(G.nodes())
    print(f"\n== {name} ==")
    print("type:", type(G))
    print("#nodes:", len(nodes))
    print("W:", _world_fields(getattr(G, "W", None)))

    for i, n in enumerate(nodes[:max_nodes]):
        op = _fmt_op(G.node_opname(n))
        ins = list(G.node_inputs(n))
        outs = list(G.node_outputs(n))
        print(f"[{i}] op={op}")
        print("   in:", _tid_list(ins))
        print("   out:", _tid_list(outs))
        # placements exist in compact mode
        if hasattr(G, "node_placements"):
            pls = list(G.node_placements(n))
            print("   placements:", len(pls), "sample:", pls[:3])
        kw = {}
        if hasattr(G, "node_kwargs"):
            try:
                kw = dict(G.node_kwargs(n))
            except Exception:
                kw = {}
        if kw:
            keys = list(kw.keys())
            preview = {k: kw[k] for k in keys[:8]}
            print("   kwargs:", preview)

    if len(nodes) > max_nodes:
        print(f"... ({len(nodes) - max_nodes} more nodes)")


def print_tensors(G: Any, name: str, max_tensors: int) -> None:
    tensors = list(G.tensors())
    tids = sorted({int(t.tid) for t in tensors})
    tid2lv = getattr(G, "_tid2lv", None)

    print(f"\n-- tensors {name} --")
    print("#tensor objects:", len(tensors), "#unique tids:", len(tids))
    if tids:
        print("tid range:", (tids[0], tids[-1]))
    print("_tid2lv:", type(tid2lv), (len(tid2lv) if isinstance(tid2lv, dict) else ""))

    shown = 0
    for tid in tids:
        t_any = next(t for t in tensors if int(t.tid) == tid)
        shp = list(G.tensor_shape(t_any))
        init = bool(G.is_initialized(t_any))

        lv = None
        if isinstance(tid2lv, dict):
            lv = tid2lv.get(tid)

        if lv is None:
            print(f"tid={tid} shape={shp} init={init}")
        else:
            ft_shape = getattr(lv, "ft_shape", None)
            slcmap = getattr(lv, "slcmap", None)
            valmap = getattr(lv, "valmap", None)
            flags = {k: getattr(lv, k) for k in ["is_grad", "is_loss", "is_attr"] if hasattr(lv, k)}
            print(f"tid={tid} shape={shp} init={init} flags={flags} ft_shape={ft_shape} slcmap={slcmap} valmap={valmap}")

        shown += 1
        if shown >= max_tensors:
            break

    if len(tids) > max_tensors:
        print(f"... ({len(tids) - max_tensors} more tids)")


def infer_and_print_lineages(Gs: Any, Gp: Any, *, full: bool, max_lineages: int = 60) -> None:
    """Infer and print lineages.

    - full=False: only align original ops and emit Ts==Tps (no slice_map computation)
    - full=True: call get_ordered_lineages (computes slice_map; can assert)
    """
    if full:
        from nnscaler_backend.build_lineage import get_ordered_lineages  # type: ignore

        print("\n== inferred lineages (FULL; includes slice_map) ==")
        try:
            lineages = get_ordered_lineages(Gs, Gp)
        except Exception as e:
            print("(lineage-full) failed:", repr(e))
            return
    else:
        from nnscaler_backend import build_lineage as bl  # type: ignore

        print("\n== inferred lineages (COARSE; Ts==Tps only) ==")
        # Mirror build_lineage.get_ordered_lineages up to aligned-op pairing.
        Gs_alignable_ops = [n for n in Gs.nodes() if bl._is_original_op(Gs.node_opname(n))]
        Gp_alignable_ops = [n for n in Gp.nodes() if bl._is_original_op(Gp.node_opname(n))]
        try:
            lineages = bl._infer_lineages_from_alignable_ops(Gs_alignable_ops, Gp_alignable_ops, Gs, Gp)
        except Exception as e:
            print("(lineage-coarse) failed:", repr(e))
            return

    print("#lineages:", len(lineages))
    for i, l in enumerate(lineages[:max_lineages]):
        Ts = getattr(l, "Ts")
        Tps = getattr(l, "Tps")
        src = getattr(l, "src", None)
        full_shape = getattr(l, "full_shape", None)
        slice_map = getattr(l, "slice_map", None)

        ts_tid = getattr(Ts, "tid", None)
        tp_tids = [getattr(tp, "tid", None) for tp in (list(Tps) if Tps is not None else [])]
        tp_ranks = [getattr(tp, "rank", None) for tp in (list(Tps) if Tps is not None else [])]

        print(f"[{i}] src={src} Ts(tid={ts_tid}) == {len(tp_tids)} Tps (tids sample={tp_tids[:6]}, ranks sample={tp_ranks[:6]})")
        if full_shape is not None:
            print("    full_shape:", full_shape)
        if isinstance(slice_map, dict) and slice_map:
            keys = list(slice_map.keys())
            print("    slice_map keys sample:", keys[:3])

    if len(lineages) > max_lineages:
        print(f"... ({len(lineages) - max_lineages} more lineages)")


def find_lineages_for_ts_tid(lineages: Sequence[Any], ts_tid: int) -> List[Any]:
    out: List[Any] = []
    for l in lineages:
        Ts = getattr(l, "Ts", None)
        if Ts is None:
            continue
        if getattr(Ts, "tid", None) == ts_tid:
            out.append(l)
    return out


def main() -> None:
    args = parse_args()

    v = load_graphs_from_disk(args.sm_pkl, args.pm_pkl)
    Gs, Gp = load_compact_graphs(v)

    print_nodes(Gs, "Gs (single)", args.max_nodes)
    print_nodes(Gp, "Gp (parallel)", args.max_nodes)

    print_tensors(Gs, "Gs", args.max_tensors)
    print_tensors(Gp, "Gp", args.max_tensors)

    if args.focus_tid is not None:
        print_focus(Gs, Gp, args.focus_tid, args.focus_depth)

    if not args.no_lineages:
        if args.lineages_from_expanded:
            print("\n(note) inferring lineages from expanded graphs (per-rank)")
            GsE, GpE = load_expanded_graphs(v)
            # Always compute coarse lineages for focus filtering (cheap), even if full mode requested.
            from nnscaler_backend import build_lineage as bl  # type: ignore
            Gs_alignable_ops = [n for n in GsE.nodes() if bl._is_original_op(GsE.node_opname(n))]
            Gp_alignable_ops = [n for n in GpE.nodes() if bl._is_original_op(GpE.node_opname(n))]
            coarse = bl._infer_lineages_from_alignable_ops(Gs_alignable_ops, Gp_alignable_ops, GsE, GpE)

            infer_and_print_lineages(GsE, GpE, full=args.lineage_full)

            if args.focus_tid is not None:
                hits = find_lineages_for_ts_tid(coarse, args.focus_tid)
                print("\n== focus lineage (COARSE) ==")
                if not hits:
                    print("no coarse lineage found for Ts tid", args.focus_tid)
                else:
                    for l in hits:
                        Ts = l.Ts
                        Tps = list(l.Tps)
                        print(
                            f"Ts(tid={Ts.tid}) == {len(Tps)} Tps",
                            "tids sample=", [tp.tid for tp in Tps[:8]],
                            "ranks sample=", [tp.rank for tp in Tps[:8]],
                        )
        else:
            infer_and_print_lineages(Gs, Gp, full=args.lineage_full)


if __name__ == "__main__":
    main()
