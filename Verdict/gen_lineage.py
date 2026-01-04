"""Generate required lineage constraints for observable output tensors.

Route A implementation:
- Load compact graphs for tensor lineage-view metadata (slcmap/valmap/ft_shape).
- Load expanded (per-rank) graphs to align original ops and infer coarse Ts==Tps.
- By default, automatically choose observable tensors as *aligned leaves*:
    leaf/output tensors in the SM graph that also appear in the inferred coarse
    lineage alignment. This avoids picking outputs that cannot be aligned.
- For each observable tensor, restrict obligations to the full backward closure
    (transitive dependencies) in the SM compact graph.

Run (must be in conda env verdict):
  conda run -n verdict python Verdict/gen_lineage.py \
    --sm-pkl <single.pkl> --pm-pkl <tp.pkl> --obs-tid 15 \
        --format json

Notes:
- This script does NOT attempt to compute slice_map like build_lineage.get_ordered_lineages,
  because that path can assert on shape assumptions for some graphs.
- Instead, it directly attaches per-tensor slcmap/valmap from compact graphs.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SM_GRAPH = ROOT / "genmodel" / "mgeners" / "mlp_mgener_dp1_pp1_tp1_nm1_gbs128_dim128_ly1.pkl"
DEFAULT_PM_GRAPH = ROOT / "genmodel" / "mgeners" / "mlp_mgener_dp1_pp1_tp8_nm1_gbs128_dim128_ly1.pkl"


@dataclass(frozen=True)
class SliceMapView:
    # [(start,end) for each dimension]
    slcmap: List[Tuple[int, int]]


@dataclass(frozen=True)
class LineageViewMeta:
    is_grad: bool
    is_loss: bool
    is_attr: bool
    ft_shape: List[int]
    slcmap: List[Tuple[int, int]]
    valmap: Tuple[int, int]


@dataclass(frozen=True)
class TensorRef:
    tid: int
    rank: Optional[int] = None


@dataclass(frozen=True)
class TensorWithMeta:
    tid: int
    rank: Optional[int]
    shape: Optional[List[int]]
    initialized: Optional[bool]
    lv: Optional[LineageViewMeta]


@dataclass(frozen=True)
class LineageConstraint:
    ts: TensorWithMeta
    tps: List[TensorWithMeta]


@dataclass(frozen=True)
class OutputForObs:
    obs_tid: int
    sm_backward_slice_tids: List[int]
    constraints: List[LineageConstraint]


@dataclass(frozen=True)
class Output:
    results: List[OutputForObs]


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=(
            "Generate lineage constraints for observable SM output tensor ids. "
            "Default behavior picks aligned leaf outputs automatically."
        )
    )
    p.add_argument("--sm-pkl", default=str(DEFAULT_SM_GRAPH), help="Path to SM graph pickle")
    p.add_argument("--pm-pkl", default=str(DEFAULT_PM_GRAPH), help="Path to PM graph pickle")
    g = p.add_mutually_exclusive_group(required=False)
    g.add_argument(
        "--obs-tid",
        type=int,
        default=None,
        help=(
            "Focused SM output tensor id. If provided, it must be alignable (appear in inferred coarse lineages). "
            "Overrides --auto-obs."
        ),
    )
    g.add_argument(
        "--auto-obs",
        choices=["aligned-leaves", "leaves"],
        default="aligned-leaves",
        help=(
            "How to choose observable SM output tids when --obs-tid is not provided. "
            "Default: aligned-leaves. "
            "aligned-leaves = leaf/output tensors (produced but never consumed) that also appear in inferred coarse lineages. "
            "leaves = all leaf/output tensors (may include non-alignable outputs)."
        ),
    )
    p.add_argument(
        "--format",
        choices=["json", "text"],
        default="json",
        help="Output format",
    )
    p.add_argument(
        "--only-obs",
        action="store_true",
        help="Only emit lineage constraints whose Ts.tid == obsTid (ignore dependencies).",
    )
    return p.parse_args()


def load_verifier(sm_path: str, pm_path: str):
    import sys

    sys.path.extend([str(ROOT), str(ROOT / "genmodel"), str(ROOT / "Verdict")])

    from verdict.config import Config  # type: ignore
    from verdict.verifier import StageParallelVerifier  # type: ignore
    from nnscaler_backend import nnScalerGraphBackend  # type: ignore
    from z3_backend import z3Backend  # type: ignore
    from analyze_graph import prepare  # type: ignore

    Config.update_from_args([])
    prepare(Config)

    return StageParallelVerifier(
        Gs_path=str(sm_path),
        Ws_path=None,
        Gp_path=str(pm_path),
        Wp_path=None,
        graph_backend=nnScalerGraphBackend,
        symbolic_backend=z3Backend,
    )


def load_compact_graphs(v) -> Tuple[Any, Any]:
    return v.get_graph_compact()


def load_expanded_graphs(v) -> Tuple[Any, Any]:
    return v.get_graph()


def _build_producer_index(G: Any) -> Dict[int, List[int]]:
    prod: Dict[int, List[int]] = {}
    for i, n in enumerate(G.nodes()):
        for t in G.node_outputs(n):
            prod.setdefault(int(t.tid), []).append(i)
    return prod


def _build_consumer_index(G: Any) -> Dict[int, List[int]]:
    cons: Dict[int, List[int]] = {}
    for i, n in enumerate(G.nodes()):
        for t in G.node_inputs(n):
            cons.setdefault(int(t.tid), []).append(i)
    return cons


def leaf_output_tids(G: Any) -> List[int]:
    """Leaf/output tensors in the dataflow sense.

    Definition (SM graph): tids that are produced by some node output and never
    appear as an input to any node.
    """
    prod = _build_producer_index(G)
    cons = _build_consumer_index(G)
    leaves = [tid for tid in prod.keys() if tid not in cons or not cons[tid]]
    return sorted(set(int(x) for x in leaves))


def backward_closure_tids(G: Any, root_tid: int) -> List[int]:
    prod = _build_producer_index(G)
    seen_tids = {int(root_tid)}
    frontier = {int(root_tid)}
    # Full transitive closure (no depth limit).
    while frontier:
        next_frontier: set[int] = set()
        for tid in list(frontier):
            for node_idx in prod.get(tid, []):
                node = G.nodes()[node_idx]
                for t_in in G.node_inputs(node):
                    t_id = int(t_in.tid)
                    if t_id not in seen_tids:
                        seen_tids.add(t_id)
                        next_frontier.add(t_id)
        frontier = next_frontier
    return sorted(seen_tids)


def _lv_from_graph_by_tid(G: Any, tid: int) -> Optional[LineageViewMeta]:
    tid2lv = getattr(G, "_tid2lv", None)
    if not isinstance(tid2lv, dict):
        return None
    lv = tid2lv.get(int(tid))
    if lv is None:
        return None

    def _to_int_pair(p: Any) -> Tuple[int, int]:
        a, b = p
        return int(a), int(b)

    slc = getattr(lv, "slcmap", None)
    if slc is None:
        slc_list: List[Tuple[int, int]] = []
    else:
        slc_list = [_to_int_pair(x) for x in list(slc)]

    val = getattr(lv, "valmap", None)
    valmap = (0, 1) if val is None else (int(val[0]), int(val[1]))

    ft = getattr(lv, "ft_shape", None)
    ft_shape = [] if ft is None else [int(x) for x in list(ft)]

    return LineageViewMeta(
        is_grad=bool(getattr(lv, "is_grad", False)),
        is_loss=bool(getattr(lv, "is_loss", False)),
        is_attr=bool(getattr(lv, "is_attr", False)),
        ft_shape=ft_shape,
        slcmap=slc_list,
        valmap=valmap,
    )


def _shape_init_from_graph_by_tid(G: Any, tid: int) -> Tuple[Optional[List[int]], Optional[bool]]:
    # Graph interface requires a Tensor object to query; pick any.
    tensors = list(G.tensors())
    t_any = next((t for t in tensors if int(getattr(t, "tid", -1)) == int(tid)), None)
    if t_any is None:
        return None, None
    try:
        shp = [int(x) for x in list(G.tensor_shape(t_any))]
    except Exception:
        shp = None
    try:
        init = bool(G.is_initialized(t_any))
    except Exception:
        init = None
    return shp, init


def tensor_with_meta(G: Any, tid: int, rank: Optional[int] = None) -> TensorWithMeta:
    shp, init = _shape_init_from_graph_by_tid(G, tid)
    lv = _lv_from_graph_by_tid(G, tid)
    return TensorWithMeta(tid=int(tid), rank=rank, shape=shp, initialized=init, lv=lv)


def infer_coarse_lineages_from_expanded(GsE: Any, GpE: Any) -> List[Any]:
    # Use internal helper: align original ops, emit Ts==Tps for each input/output.
    from nnscaler_backend import build_lineage as bl  # type: ignore

    Gs_alignable_ops = [n for n in GsE.nodes() if bl._is_original_op(GsE.node_opname(n))]
    Gp_alignable_ops = [n for n in GpE.nodes() if bl._is_original_op(GpE.node_opname(n))]
    return bl._infer_lineages_from_alignable_ops(Gs_alignable_ops, Gp_alignable_ops, GsE, GpE)


def _lineage_key(l: Any) -> Tuple[int, Tuple[Tuple[int, int], ...]]:
    Ts = getattr(l, "Ts")
    Tps = list(getattr(l, "Tps"))
    key_tps = tuple(sorted((int(tp.rank), int(tp.tid)) for tp in Tps))
    return int(Ts.tid), key_tps


def compute_required_lineages(
    *,
    sm_pkl: str,
    pm_pkl: str,
    obs_tid: Optional[int],
    auto_obs: Optional[str],
    only_obs: bool,
) -> Output:
    v = load_verifier(sm_pkl, pm_pkl)
    GsE, GpE = load_expanded_graphs(v)

    # Use compact SM graph only for backward-slice computation (compact is fast and stable).
    # Meta for Ts/Tp will be taken from expanded graphs so per-rank tids have lv/shape.
    GsC, _GpC = load_compact_graphs(v)

    coarse = infer_coarse_lineages_from_expanded(GsE, GpE)

    # Index coarse lineages by Ts tid for fast filtering.
    lineages_by_ts: Dict[int, List[Any]] = {}
    for l in coarse:
        Ts = getattr(l, "Ts")
        lineages_by_ts.setdefault(int(Ts.tid), []).append(l)

    if obs_tid is not None:
        obs_tids = [int(obs_tid)]
    else:
        if auto_obs is None:
            auto_obs = "aligned-leaves"
        candidate = leaf_output_tids(GsC)
        if auto_obs == "aligned-leaves":
            obs_tids = [tid for tid in candidate if tid in lineages_by_ts]
        else:
            obs_tids = candidate

    # Alignment is required for proof obligations.
    # If user explicitly chose a non-alignable obs tid, fail loudly.
    if obs_tid is not None and int(obs_tid) not in lineages_by_ts:
        raise ValueError(f"obs_tid={int(obs_tid)} does not appear in inferred coarse lineages; cannot align SM to PM")

    results: List[OutputForObs] = []
    for obs in obs_tids:
        needed_ts_tids = {int(obs)} if only_obs else set(backward_closure_tids(GsC, obs))

        # dedup and filter
        uniq: Dict[Tuple[int, Tuple[Tuple[int, int], ...]], Any] = {}
        # iterate only relevant Ts tids to cut work
        for ts_tid in needed_ts_tids:
            for l in lineages_by_ts.get(int(ts_tid), []):
                k = _lineage_key(l)
                uniq.setdefault(k, l)

        constraints: List[LineageConstraint] = []
        for l in uniq.values():
            Ts = getattr(l, "Ts")
            Tps = list(getattr(l, "Tps"))

            ts_meta = tensor_with_meta(GsE, int(Ts.tid), rank=None)
            tps_meta: List[TensorWithMeta] = [
                tensor_with_meta(GpE, int(tp.tid), rank=int(tp.rank)) for tp in sorted(Tps, key=lambda x: int(x.rank))
            ]
            constraints.append(LineageConstraint(ts=ts_meta, tps=tps_meta))

        constraints.sort(key=lambda c: c.ts.tid)
        results.append(
            OutputForObs(
                obs_tid=int(obs),
                sm_backward_slice_tids=sorted(needed_ts_tids),
                constraints=constraints,
            )
        )

    results.sort(key=lambda r: r.obs_tid)
    return Output(results=results)


def _print_text(out: Output) -> None:
    print("obs_tids:", [r.obs_tid for r in out.results])
    for r in out.results:
        print("\n=== obs_tid:", r.obs_tid, "===")
        print("sm_backward_slice_tids:", r.sm_backward_slice_tids)
        print("required lineages:")
        for c in r.constraints:
            ts = c.ts
            print(
                f"- Ts tid={ts.tid} shape={ts.shape} init={ts.initialized} "
                f"lv.valmap={ts.lv.valmap if ts.lv else None} lv.slcmap={ts.lv.slcmap if ts.lv else None}"
            )
            for tp in c.tps:
                lv = tp.lv
                print(
                    f"    Tp rank={tp.rank} tid={tp.tid} shape={tp.shape} init={tp.initialized} "
                    f"valmap={(lv.valmap if lv else None)} slcmap={(lv.slcmap if lv else None)}"
                )


def main() -> None:
    args = parse_args()
    out = compute_required_lineages(
        sm_pkl=args.sm_pkl,
        pm_pkl=args.pm_pkl,
        obs_tid=args.obs_tid,
        auto_obs=getattr(args, "auto_obs", None),
        only_obs=bool(args.only_obs),
    )

    if args.format == "json":
        print(json.dumps(asdict(out), ensure_ascii=False, indent=2))
    else:
        _print_text(out)


if __name__ == "__main__":
    # When piping to tools like `head`, the reader may close early.
    # Let SIGPIPE terminate silently instead of printing noisy BrokenPipeError.
    try:
        import signal

        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    except Exception:
        pass
    try:
        import sys

        # Make stdout flush frequently so BrokenPipe happens at write time.
        sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass
    try:
        main()
    except BrokenPipeError:
        # Common when piping to `head`, etc. Exit immediately and quietly.
        try:
            import os
            import sys

            try:
                sys.stdout.close()
            finally:
                os._exit(0)
        except Exception:
            raise
