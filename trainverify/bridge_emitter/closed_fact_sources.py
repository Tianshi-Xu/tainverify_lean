"""Exact retained-fact TIDs and ordered source authority for closed renderers."""
from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .parser import GoalIR
    from .relation_compiler import ClosedRelationFactRecord


def fact_tids(fact: object) -> tuple[set[int], set[int]]:
    """Return protected SM/PM TIDs, rejecting unsupported types and metadata."""
    # Keep compiler imports lazy, matching renderer loading in both import modes.
    try:
        from .relation_compiler import (
            ClosedRelationFactRecord, ClosedTensorShapeFactRecord,
            ClosedTensorEqFactRecord, ClosedGatherFactRecord,
            ClosedPackedCuFactRecord, ClosedLabelBoundFactRecord,
        )
    except ImportError:
        from relation_compiler import (
            ClosedRelationFactRecord, ClosedTensorShapeFactRecord,
            ClosedTensorEqFactRecord, ClosedGatherFactRecord,
            ClosedPackedCuFactRecord, ClosedLabelBoundFactRecord,
        )

    if type(fact) is ClosedRelationFactRecord:
        if fact.kind in {"sharded", "chunked", "reduction", "replicated", "ordinary"}:
            return {fact.sm_tid}, set(fact.pm_tids)
        if fact.kind == "joined":
            if fact.joined_pm_tid is None:
                raise ValueError("joined retained fact lacks PM TID")
            return {fact.sm_tid}, {fact.joined_pm_tid}
        if fact.kind == "zigzag":
            if fact.metadata_tid is None:
                raise ValueError("zigzag retained fact lacks metadata TID")
            return {fact.sm_tid}, {*fact.pm_tids, fact.metadata_tid}
        if fact.kind == "joined_ordinary":
            if fact.joined_pm_tid is None:
                raise ValueError("joined ordinary retained fact lacks PM TID")
            return {fact.sm_tid}, {*fact.pm_tids, fact.joined_pm_tid}
        if fact.kind == "joined_indexed_stack_dim1":
            if fact.joined_pm_tid is None or not fact.source_tid_triples:
                raise ValueError("joined indexed-stack retained fact is incomplete")
            sm, pm = {fact.sm_tid}, {*fact.pm_tids, fact.joined_pm_tid}
            for source_sm, source_pm0, source_pm1 in fact.source_tid_triples:
                sm.add(source_sm)
                pm.update((source_pm0, source_pm1))
            return sm, pm
        if fact.kind == "label_chunks":
            return set(), {fact.sm_tid, *fact.pm_tids}
        raise ValueError(f"unsupported retained relation fact kind: {fact.kind!r}")
    if type(fact) is ClosedTensorShapeFactRecord:
        if fact.side not in {"sm", "pm"}:
            raise ValueError("retained tensor-shape fact has invalid side")
        return ({fact.tid}, set()) if fact.side == "sm" else (set(), {fact.tid})
    if type(fact) is ClosedTensorEqFactRecord:
        if fact.left_side not in {"sm", "pm"} or fact.right_side not in {"sm", "pm"}:
            raise ValueError("retained tensor-equality fact has invalid side")
        sm, pm = set(), set()
        (sm if fact.left_side == "sm" else pm).add(fact.left_tid)
        (sm if fact.right_side == "sm" else pm).add(fact.right_tid)
        return sm, pm
    if type(fact) is ClosedGatherFactRecord:
        return {fact.sm_tid}, {fact.pm_rank0_tid, fact.pm_rank1_tid}
    if type(fact) in {ClosedPackedCuFactRecord, ClosedLabelBoundFactRecord}:
        if fact.side not in {"sm", "pm"}:
            raise ValueError("retained side-specific authority fact has invalid side")
        return ({fact.tid}, set()) if fact.side == "sm" else (set(), {fact.tid})
    raise ValueError(f"unsupported retained fact record: {type(fact).__name__}")


def latest_ref(ir: GoalIR, side: str, tid: int, end: int) -> str:
    """Find the last writer/output slot in the side's prefix ending before end."""
    nodes = ir.sm_nodes if side == "sm" else ir.pm_nodes
    latest = f"init:{tid}"
    for index, node in enumerate(nodes[:end]):
        for slot, out in enumerate(node.outs):
            if out == tid:
                latest = f"{side}:{index}:{slot}"
    return latest


def source_exact(
    ir: GoalIR,
    fact: ClosedRelationFactRecord,
    sm_end: int,
    pm_end: int,
    *,
    context: str,
) -> None:
    """Validate flat source metadata and latest writers at explicit boundaries."""
    source = fact.source
    if (source.layout != fact.kind or source.gather_dim != fact.gather_dim
            or source.source_step_triples):
        raise ValueError(f"{context} source layout/axis mismatch")
    expected = (
        latest_ref(ir, "sm", fact.sm_tid, sm_end),
        *(latest_ref(ir, "pm", tid, pm_end) for tid in fact.pm_tids),
    )
    if source.step_triple != expected:
        raise ValueError(f"{context} source is not the latest ordered TID authority")
    joined = (
        None if fact.joined_pm_tid is None
        else latest_ref(ir, "pm", fact.joined_pm_tid, pm_end)
    )
    if source.joined_pm_step != joined:
        raise ValueError(f"{context} joined source is not the latest writer")
