"""Generic full-topology certificate composers.

The first registered composition rule covers a two-rank hidden-sharded
embedding followed by AllToAll(idim=1, odim=0).  Every tensor id and dimension
is derived from GoalIR; no model or layer identifiers are embedded here.
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Optional

try:
    from .parser import GoalIR, Node
except ImportError:
    from parser import GoalIR, Node


class CompositionCode(str, Enum):
    TOPOLOGY_MISMATCH = "composition.topology-mismatch"
    SHAPE_MISMATCH = "composition.shape-mismatch"
    UNSUPPORTED_TOPOLOGY = "composition.unsupported-topology"


@dataclass(frozen=True)
class CompositionDiagnostic:
    code: CompositionCode
    message: str
    node_index: Optional[int] = None


@dataclass(frozen=True)
class CompositionResult:
    rule_id: Optional[str]
    lean_source: str
    diagnostics: tuple[CompositionDiagnostic, ...]

    @property
    def supported(self) -> bool:
        return not self.diagnostics


def _failure(
    code: CompositionCode, message: str, node_index: Optional[int] = None
) -> CompositionResult:
    return CompositionResult(None, "", (CompositionDiagnostic(code, message, node_index),))


def _shape_map(entries: list) -> dict[int, list[int]]:
    return {int(tid): [int(value) for value in shape] for tid, shape in entries}


def _shape_text(shape: list[int]) -> str:
    return "[" + ", ".join(str(value) for value in shape) + "]"


def _node_text(node: Node) -> str:
    fields = [
        f"rank := {node.rank}",
        f'op := "OpName.{node.op}"',
        "ins := [" + ", ".join(str(tid) for tid in node.ins) + "]",
        "outs := [" + ", ".join(str(tid) for tid in node.outs) + "]",
    ]
    if node.params:
        fields.append("params := [" + ", ".join(str(p) for p in node.params) + "]")
    return "{ " + ", ".join(fields) + " }"


def _match_hidden_embedding_alltoall_two(ir: GoalIR):
    if ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2:
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            f"expected graph rank headers SM=1 and PM=2, got SM={ir.sm_num_ranks} PM={ir.pm_num_ranks}",
        )
    if ir.prereqs:
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            "full-topology rule requires no computed prerequisite boundary",
        )
    if len(ir.sm_nodes) != 1:
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            f"expected one SM node, got {len(ir.sm_nodes)}",
        )
    sm = ir.sm_nodes[0]
    if (
        sm.op != "FW_embedding"
        or sm.rank != 0
        or len(sm.ins) != 2
        or len(sm.outs) != 1
        or bool(sm.params)
    ):
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            "SM node is not an unparameterized single-output FW_embedding",
            0,
        )
    if len(ir.pm_nodes) != 4:
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            f"expected four PM nodes, got {len(ir.pm_nodes)}",
        )
    e0, e1, a0, a1 = ir.pm_nodes
    expected_embedding = (
        e0.op == e1.op == "FW_embedding"
        and e0.rank == 0
        and e1.rank == 1
        and len(e0.ins) == len(e1.ins) == 2
        and len(e0.outs) == len(e1.outs) == 1
        and e0.ins[0] == e1.ins[0] == sm.ins[0]
        and not (e0.params or e1.params)
    )
    if not expected_embedding:
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            "PM prefix is not the two rank-local embedding projections",
            0,
        )
    mids = [e0.outs[0], e1.outs[0]]
    for index, node in ((2, a0), (3, a1)):
        if (
            node.op != "AllToAllPrim"
            or node.rank != index - 2
            or node.ins != mids
            or len(node.outs) != 1
            or node.params != [1, 0]
        ):
            return _failure(
                CompositionCode.TOPOLOGY_MISMATCH,
                "expected rank-local AllToAllPrim over both embedding shards with params [1, 0]",
                index,
            )
    pieces = [(int(rank), int(tid)) for rank, tid in ir.lineage.tps]
    expected_pieces = [(0, a0.outs[0]), (1, a1.outs[0])]
    if ir.lineage.ts != sm.outs[0] or pieces != expected_pieces:
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            "lineage outputs do not match the SM embedding and PM AllToAll outputs",
        )
    role_tids = [
        sm.ins[0],
        sm.ins[1],
        sm.outs[0],
        e0.ins[1],
        e1.ins[1],
        e0.outs[0],
        e1.outs[0],
        a0.outs[0],
        a1.outs[0],
    ]
    if len(set(role_tids)) != len(role_tids):
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            "embedding/weight/intermediate/output tensor roles must have distinct tids",
        )
    if ir.lineage.replicated or (ir.lineage.gatherDim or 0) != 0:
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            "output relation must gather the two AllToAll outputs along dimension 0",
        )

    for side, entries in (("SM", ir.sm_shapes), ("PM", ir.pm_shapes)):
        shape_tids = [int(tid) for tid, _shape in entries]
        if len(set(shape_tids)) != len(shape_tids):
            return _failure(
                CompositionCode.SHAPE_MISMATCH,
                f"{side} InitShapes contains a duplicate shape tid",
            )
    sm_shapes = _shape_map(ir.sm_shapes)
    pm_shapes = _shape_map(ir.pm_shapes)
    required = [sm.ins[0], sm.ins[1]]
    if any(tid not in sm_shapes for tid in required):
        return _failure(CompositionCode.SHAPE_MISMATCH, "missing SM input shape")
    if any(tid not in pm_shapes for tid in (e0.ins[0], e0.ins[1], e1.ins[1])):
        return _failure(CompositionCode.SHAPE_MISMATCH, "missing PM input shape")
    ids_shape = sm_shapes[sm.ins[0]]
    full_weight_shape = sm_shapes[sm.ins[1]]
    pm_ids_shape = pm_shapes[e0.ins[0]]
    shard0_shape = pm_shapes[e0.ins[1]]
    shard1_shape = pm_shapes[e1.ins[1]]
    if (
        len(ids_shape) != 1
        or len(full_weight_shape) != 2
        or pm_ids_shape != ids_shape
        or len(shard0_shape) != 2
        or shard1_shape != shard0_shape
        or shard0_shape[0] != full_weight_shape[0]
        or shard0_shape[1] * 2 != full_weight_shape[1]
        or ids_shape[0] % 2 != 0
    ):
        return _failure(
            CompositionCode.SHAPE_MISMATCH,
            "embedding shapes do not form two equal hidden-dimension shards",
        )
    seq = ids_shape[0]
    half_seq = seq // 2
    vocab = full_weight_shape[0]
    hidden = full_weight_shape[1]
    shard_hidden = shard0_shape[1]
    if half_seq <= 0 or vocab <= 0 or shard_hidden <= 0:
        return _failure(
            CompositionCode.SHAPE_MISMATCH,
            "embedding theorem requires positive token, vocabulary, and shard-hidden dimensions",
        )
    if ir.lineage.tsShape != [seq, hidden] or ir.lineage.tpShapes != [
        [half_seq, hidden],
        [half_seq, hidden],
    ]:
        return _failure(
            CompositionCode.SHAPE_MISMATCH,
            "lineage shapes do not match embedding/AllToAll reconstruction",
        )
    required_init_ids = {sm.ins[0], sm.ins[1]}
    if not required_init_ids.issubset(set(ir.full_init_goal_ids)):
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            "required embedding input InitGoals are absent from the full-init contract",
        )
    ids_init = ir.init_lineages.get(sm.ins[0])
    weight_init = ir.init_lineages.get(sm.ins[1])
    if (
        ids_init is None
        or ids_init.ts != sm.ins[0]
        or ids_init.tsShape != ids_shape
        or ids_init.tps != [(0, sm.ins[0])]
        or ids_init.tpShapes != [ids_shape]
        or (ids_init.gatherDim or 0) != 0
        or ids_init.replicated
    ):
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            "token InitGoal is not the required singleton reconstruction",
        )
    if (
        weight_init is None
        or weight_init.ts != sm.ins[1]
        or weight_init.tsShape != full_weight_shape
        or weight_init.tps != [(0, e0.ins[1]), (1, e1.ins[1])]
        or weight_init.tpShapes != [shard0_shape, shard1_shape]
        or weight_init.gatherDim != 1
        or weight_init.replicated
    ):
        return _failure(
            CompositionCode.TOPOLOGY_MISMATCH,
            "weight InitGoal is not the required rank-ordered hidden-dimension reconstruction",
        )
    return {
        "sm": sm,
        "e0": e0,
        "e1": e1,
        "a0": a0,
        "a1": a1,
        "seq": seq,
        "half_seq": half_seq,
        "vocab": vocab,
        "hidden": hidden,
        "shard_hidden": shard_hidden,
        "ids_shape": ids_shape,
        "full_weight_shape": full_weight_shape,
        "shard_shape": shard0_shape,
    }


def _render_hidden_embedding_alltoall_two(
    ir: GoalIR, match: dict, module_prefix: str
) -> str:
    n = ir.n
    sm, e0, e1, a0, a1 = (match[key] for key in ("sm", "e0", "e1", "a0", "a1"))
    ids, full_weight = sm.ins
    sm_out = sm.outs[0]
    weight0, weight1 = e0.ins[1], e1.ins[1]
    mid0, mid1 = e0.outs[0], e1.outs[0]
    out0, out1 = a0.outs[0], a1.outs[0]
    seq = match["seq"]
    half_seq = match["half_seq"]
    vocab = match["vocab"]
    hidden = match["hidden"]
    shard_hidden = match["shard_hidden"]
    ids_shape = _shape_text(match["ids_shape"])
    full_weight_shape = _shape_text(match["full_weight_shape"])
    shard_shape = _shape_text(match["shard_shape"])
    embedded_shape = _shape_text([seq, shard_hidden])
    piece_shape = _shape_text([half_seq, hidden])
    nodes = ",\n     ".join(_node_text(node) for node in ir.pm_nodes)

    return f'''/- AUTO-GENERATED by bridge_emitter.composer.
   rule: embedding-hidden-alltoall-two; goal: {n}. -/
import {module_prefix}.Goal_{n}
import {module_prefix}.BridgeKit
import denote.EmbeddingHiddenShard

set_option linter.style.longLine false
set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedCompiled

theorem compiled_denote_sm_goal_{n}_{sm_out} (initSM : Store) :
    denoteGraph sm_goal_{n} initSM {sm_out} = fw_embedding (initSM {ids}) (initSM {full_weight}) := by
  unfold denoteGraph
  simp only [sm_goal_{n}, List.foldl]
  exact applyNode_fw_embedding_out sm_goal_{n} initSM 0 {ids} {full_weight} {sm_out}

theorem compiled_denote_pm_goal_{n}_outputs (initPM : Store) :
    denoteGraph pm_goal_{n} initPM {out0} =
      allToAllPrimWithDims 2 0
        [fw_embedding (initPM {ids}) (initPM {weight0}),
         fw_embedding (initPM {ids}) (initPM {weight1})] 1 0 ∧
    denoteGraph pm_goal_{n} initPM {out1} =
      allToAllPrimWithDims 2 1
        [fw_embedding (initPM {ids}) (initPM {weight0}),
         fw_embedding (initPM {ids}) (initPM {weight1})] 1 0 := by
  set g : GraphDecl := {{ numRanks := 2, nodes :=
    [{nodes}] }} with hg
  have hpm : pm_goal_{n} = g := by rfl
  rw [hpm]
  set n0 : NodeDecl := {_node_text(e0)}
  set n1 : NodeDecl := {_node_text(e1)}
  set n2 : NodeDecl := {_node_text(a0)}
  set n3 : NodeDecl := {_node_text(a1)}
  set S1 : Store := applyNode g initPM n0
  set S2 : Store := applyNode g S1 n1
  set S3 : Store := applyNode g S2 n2
  have hS1_{mid0} : S1 {mid0} = fw_embedding (initPM {ids}) (initPM {weight0}) := by
    exact applyNode_fw_embedding_out g initPM 0 {ids} {weight0} {mid0}
  have hS1_{ids} : S1 {ids} = initPM {ids} := by
    apply applyNode_eq_of_not_mem_outs
    decide
  have hS1_{weight1} : S1 {weight1} = initPM {weight1} := by
    apply applyNode_eq_of_not_mem_outs
    decide
  have hS2_{mid0} : S2 {mid0} = fw_embedding (initPM {ids}) (initPM {weight0}) := by
    rw [show S2 {mid0} = S1 {mid0} by
      apply applyNode_eq_of_not_mem_outs
      decide]
    exact hS1_{mid0}
  have hS2_{mid1} : S2 {mid1} = fw_embedding (initPM {ids}) (initPM {weight1}) := by
    rw [show S2 {mid1} = fw_embedding (S1 {ids}) (S1 {weight1}) by
      exact applyNode_fw_embedding_out g S1 1 {ids} {weight1} {mid1}]
    rw [hS1_{ids}, hS1_{weight1}]
  have hS3_{mid0} : S3 {mid0} = fw_embedding (initPM {ids}) (initPM {weight0}) := by
    rw [show S3 {mid0} = S2 {mid0} by
      apply applyNode_eq_of_not_mem_outs
      decide]
    exact hS2_{mid0}
  have hS3_{mid1} : S3 {mid1} = fw_embedding (initPM {ids}) (initPM {weight1}) := by
    rw [show S3 {mid1} = S2 {mid1} by
      apply applyNode_eq_of_not_mem_outs
      decide]
    exact hS2_{mid1}
  refine ⟨?_, ?_⟩
  · have hden : denoteGraph g initPM {out0} = applyNode g S3 n3 {out0} := by
      unfold denoteGraph
      simp only [hg, List.foldl]
      rfl
    rw [hden]
    rw [show applyNode g S3 n3 {out0} = S3 {out0} by
      apply applyNode_eq_of_not_mem_outs
      decide]
    rw [show S3 {out0} = allToAllPrimWithDims 2 0 [S2 {mid0}, S2 {mid1}] 1 0 by
      exact applyNode_allToAllPrimWithDims_out g S2 0 [{mid0}, {mid1}] {out0} 1 0]
    rw [hS2_{mid0}, hS2_{mid1}]
  · have hden : denoteGraph g initPM {out1} = applyNode g S3 n3 {out1} := by
      unfold denoteGraph
      simp only [hg, List.foldl]
      rfl
    rw [hden]
    rw [show applyNode g S3 n3 {out1} =
        allToAllPrimWithDims 2 1 [S3 {mid0}, S3 {mid1}] 1 0 by
      exact applyNode_allToAllPrimWithDims_out g S3 1 [{mid0}, {mid1}] {out1} 1 0]
    rw [hS3_{mid0}, hS3_{mid1}]

theorem compiled_prove_goal_{n} : goal_{n}_stmt_full := by
  intro initSM initPM hSM hPM hInit
  simp only [goal_{n}]
  have h{ids}sm : (initSM {ids}).shape = {ids_shape} :=
    hSM {ids} {ids_shape} (by native_decide)
  have h{full_weight}sm : (initSM {full_weight}).shape = {full_weight_shape} :=
    hSM {full_weight} {full_weight_shape} (by native_decide)
  have h{ids}pm : (initPM {ids}).shape = {ids_shape} :=
    hPM {ids} {ids_shape} (by native_decide)
  have h{weight0} : (initPM {weight0}).shape = {shard_shape} :=
    hPM {weight0} {shard_shape} (by native_decide)
  have h{weight1} : (initPM {weight1}).shape = {shard_shape} :=
    hPM {weight1} {shard_shape} (by native_decide)
  have hpmR : pm_goal_{n}.numRanks = 2 := rfl
  have hE0 : (fw_embedding (initPM {ids}) (initPM {weight0})).shape = {embedded_shape} := by
    rw [fw_embedding_shape, h{ids}pm, h{weight0}]
    rfl
  have hE1 : (fw_embedding (initPM {ids}) (initPM {weight1})).shape = {embedded_shape} := by
    rw [fw_embedding_shape, h{ids}pm, h{weight1}]
    rfl
  have hEhead : (([fw_embedding (initPM {ids}) (initPM {weight0}),
      fw_embedding (initPM {ids}) (initPM {weight1})].head?.map
      (fun t => t.shape)).getD []) = {embedded_shape} := by
    simp only [List.head?, Option.map, Option.getD]
    exact hE0
  have houts := compiled_denote_pm_goal_{n}_outputs initPM
  have hA0 : (allToAllPrimWithDims 2 0
      [fw_embedding (initPM {ids}) (initPM {weight0}),
       fw_embedding (initPM {ids}) (initPM {weight1})] 1 0).shape = {piece_shape} := by
    rw [allToAllPrimWithDims_shape 2 0 _ 1 0 {embedded_shape} hEhead (by decide)]
    decide
  have hA1 : (allToAllPrimWithDims 2 1
      [fw_embedding (initPM {ids}) (initPM {weight0}),
       fw_embedding (initPM {ids}) (initPM {weight1})] 1 0).shape = {piece_shape} := by
    rw [allToAllPrimWithDims_shape 2 1 _ 1 0 {embedded_shape} hEhead (by decide)]
    decide
  refine ⟨?_, ?_, ?_⟩
  · rw [compiled_denote_sm_goal_{n}_{sm_out}, fw_embedding_shape, h{ids}sm, h{full_weight}sm]
    rfl
  · simp only [List.map]
    rw [houts.1, houts.2]
    rw [hA0, hA1]
  · simp only [List.map, reconstructForGoal, Bool.false_eq_true, if_false]
    rw [compiled_denote_sm_goal_{n}_{sm_out}, houts.1, houts.2]
    have hInit' : InitGoalsHold pm_goal_{n}.numRanks initGoals initSM initPM := by
      unfold goal_{n}_full_initGoals at hInit
      exact hInit
    have hg{ids} := hInit' initGoal_{ids} (by native_decide)
    unfold InitGoalHolds at hg{ids}
    obtain ⟨_, _, hval{ids}⟩ := hg{ids}
    simp only [initGoal_{ids}, hpmR, List.map, reconstructForGoal,
      Bool.false_eq_true, if_false, reconstructWithDim_singleton] at hval{ids}
    rw [hval{ids}]
    have hg{full_weight} := hInit' initGoal_{full_weight} (by native_decide)
    unfold InitGoalHolds at hg{full_weight}
    obtain ⟨_, _, hval{full_weight}⟩ := hg{full_weight}
    simp only [initGoal_{full_weight}, hpmR, List.map, reconstructForGoal,
      Bool.false_eq_true, if_false] at hval{full_weight}
    have hreconstructW :
        reconstructWithDim 1 2 0 [initPM {weight0}, initPM {weight1}] =
          allGatherPrimDimN 1 2 0 [initPM {weight0}, initPM {weight1}] := by
      unfold reconstructWithDim
      simp only [List.head?_cons, Option.map_some, Option.getD_some, h{weight0}]
      rfl
    rw [hreconstructW] at hval{full_weight}
    rw [hval{full_weight}]
    have hreconstructOut : reconstructWithDim 0 pm_goal_{n}.numRanks 0
        [allToAllPrimWithDims 2 0
            [fw_embedding (initPM {ids}) (initPM {weight0}),
             fw_embedding (initPM {ids}) (initPM {weight1})] 1 0,
         allToAllPrimWithDims 2 1
            [fw_embedding (initPM {ids}) (initPM {weight0}),
             fw_embedding (initPM {ids}) (initPM {weight1})] 1 0] =
      allGatherPrimDimN 0 2 0
        [allToAllPrimWithDims 2 0
            [fw_embedding (initPM {ids}) (initPM {weight0}),
             fw_embedding (initPM {ids}) (initPM {weight1})] 1 0,
         allToAllPrimWithDims 2 1
            [fw_embedding (initPM {ids}) (initPM {weight0}),
             fw_embedding (initPM {ids}) (initPM {weight1})] 1 0] := by
      rw [hpmR]
      apply reconstructWithDim_cons_cons_nonscalar
      rw [hA0]
      decide
    rw [hreconstructOut]
    exact fw_embedding_hidden_shards_allToAll_two {half_seq} {vocab} {shard_hidden}
      (initPM {ids}) (initPM {weight0}) (initPM {weight1})
      (by decide) (by decide) (by decide) h{ids}pm h{weight0} h{weight1}

end TrainVerify.Denote.GeneratedCompiled
'''


def render_closed_relation_declarations(chain, namespace: str) -> str:
    """Render only the closed fact/state universe; segment proofs are separate."""

    import re

    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", namespace):
        raise ValueError(f"invalid Lean namespace: {namespace}")
    if chain is None or not chain.complete:
        raise ValueError("closed relation declarations require a complete chain plan")

    def shape_text(shape):
        return "[" + ", ".join(str(int(value)) for value in shape) + "]"

    lines = [
        "/- AUTO-GENERATED closed relation state universe. -/",
        "import denote.RelationCompiler",
        "",
        "open TrainVerify.Denote",
        "open TrainVerify.Denote.RelationCompiler",
        "",
        f"namespace TrainVerify.Denote.{namespace}",
        "",
        "set_option maxRecDepth 100000",
        "noncomputable section",
        "",
    ]
    for fact in chain.relation_facts:
        if fact.kind == "ordinary":
            constructor = (
                f".ordinary {fact.sm_tid} {fact.pm_rank0_tid} {fact.pm_rank1_tid} "
                f"{shape_text(fact.full_shape)} {shape_text(fact.shard_shape)}"
            )
        elif fact.kind == "zigzag":
            if fact.metadata_tid is None:
                raise ValueError(f"zigzag fact lacks metadata: {fact.fact_id}")
            constructor = (
                f".zigzag {fact.sm_tid} {fact.pm_rank0_tid} {fact.pm_rank1_tid} "
                f"{fact.metadata_tid} {shape_text(fact.full_shape)} "
                f"{shape_text(fact.shard_shape)}"
            )
        else:
            raise ValueError(f"unsupported closed relation fact: {fact.kind}")
        lines.extend([
            f"private def {fact.fact_id} : RelationFact :=",
            f"  {constructor}",
            "",
        ])
    for fact in chain.authority_facts:
        if fact.kind == "tensor_eq":
            constructor = (
                f".tensorEq .{fact.left_side} {fact.left_tid} "
                f".{fact.right_side} {fact.right_tid}"
            )
        elif fact.kind == "tensor_shape":
            constructor = (
                f".tensorShape .{fact.side} {fact.tid} "
                f"{_shape_text(fact.shape)}"
            )
        elif fact.kind == "gather":
            constructor = (
                f".gather {fact.sm_tid} {fact.pm_rank0_tid} {fact.pm_rank1_tid} "
                f"{fact.dim} {_shape_text(fact.full_shape)} "
                f"{_shape_text(fact.shard_shape)}"
            )
        elif fact.kind == "packed_cu":
            constructor = (
                f".packedCu .{fact.side} {fact.tid} "
                f"{fact.total_tokens} {fact.num_ranks}"
            )
        else:
            raise ValueError(f"unsupported closed authority fact: {fact.kind}")
        lines.extend([
            f"private def {fact.fact_id} : RelationFact :=",
            f"  {constructor}",
            "",
        ])
    anchor = chain.anchor_fact
    lines.extend([
        f"private def {anchor.fact_id} : RelationFact :=",
        f"  .tensorShape .{anchor.side} {anchor.tid} {shape_text(anchor.shape)}",
        "",
    ])
    known = (
        {fact.fact_id for fact in chain.relation_facts}
        | {fact.fact_id for fact in chain.authority_facts}
        | {anchor.fact_id}
    )
    for state in chain.states:
        if not state.fact_ids or any(fact_id not in known for fact_id in state.fact_ids):
            raise ValueError(f"state references unknown or empty facts: {state.state_id}")
        rendered = ", ".join(state.fact_ids)
        lines.extend([
            f"private def {state.state_id} : RelationState where",
            f"  facts := [{rendered}]",
            "  nonempty := by decide",
            "",
        ])
    lines.extend([
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ])
    return "\n".join(lines)


def render_closed_float_segment(ir: GoalIR, relation, segment_id: str) -> str:
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("float segment renderer requires a complete closed chain")
    matches = [x for x in chain.segments if x.segment_id == segment_id]
    if len(matches) != 1 or len(matches[0].transition_ids) != 1:
        raise ValueError(f"unknown or non-atomic float segment: {segment_id}")
    segment = matches[0]
    transition = {x.transition_id: x for x in relation.transition_specs}[segment.transition_ids[0]]
    if transition.lean_theorem != "TrainVerify.Denote.fw_float_allGather0_commute_2":
        raise ValueError(f"float renderer theorem mismatch: {transition.lean_theorem}")
    if len(transition.pre_facts) != 1 or len(transition.post_facts) != 1:
        raise ValueError("float transition must have one pre/post fact")
    facts = {x.source: x for x in chain.relation_facts}
    before, after = facts[transition.pre_facts[0]], facts[transition.post_facts[0]]
    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    if before.kind != "ordinary" or after.kind != "ordinary":
        raise ValueError("float renderer supports ordinary relations only")
    if len(sm_nodes) != 1 or len(pm_nodes) != 2 or any(n.op != "FW_float" for n in (*sm_nodes, *pm_nodes)):
        raise ValueError("float renderer requires one SM and two PM FW_float nodes")
    if [n.rank for n in pm_nodes] != [0, 1] or any(len(n.ins) != 1 or len(n.outs) != 1 for n in (*sm_nodes, *pm_nodes)):
        raise ValueError("float nodes have invalid rank or arity")
    if tuple(sm_nodes[0].ins + pm_nodes[0].ins + pm_nodes[1].ins) != (before.sm_tid, before.pm_rank0_tid, before.pm_rank1_tid):
        raise ValueError("float inputs do not match pre fact")
    if tuple(sm_nodes[0].outs + pm_nodes[0].outs + pm_nodes[1].outs) != (after.sm_tid, after.pm_rank0_tid, after.pm_rank1_tid):
        raise ValueError("float outputs do not match post fact")
    params = tuple(sm_nodes[0].params or ())
    if any(tuple(n.params or ()) != params for n in pm_nodes):
        raise ValueError("float params disagree")
    if (before.full_shape, before.shard_shape) != (after.full_shape, after.shard_shape):
        raise ValueError("float unexpectedly changes shape")
    states = {x.state_id: x for x in chain.states}
    pre_state, post_state = states[segment.pre_state_id], states[segment.post_state_id]
    if before.fact_id not in pre_state.fact_ids or after.fact_id not in post_state.fact_ids:
        raise ValueError("float input/output fact is not live")
    if not set(post_state.fact_ids) <= ({after.fact_id} | set(pre_state.fact_ids)):
        raise ValueError("float state introduces an unproved fact")
    sm_text = "[" + _node_text(sm_nodes[0]) + "]"
    pm_text = "[" + ", ".join(_node_text(n) for n in pm_nodes) + "]"
    full_shape, shard_shape = _shape_text(list(after.full_shape)), _shape_text(list(after.shard_shape))
    params_text = "[" + ", ".join(str(x) for x in params) + "]"
    si, p0i, p1i = before.sm_tid, before.pm_rank0_tid, before.pm_rank1_tid
    so, p0o, p1o = after.sm_tid, after.pm_rank0_tid, after.pm_rank1_tid
    return f'''private def {segment.segment_id} (smGraph pmGraph : GraphDecl) :
    ClosedDepSegmentCertificate smGraph pmGraph {pre_state.state_id} {post_state.state_id} where
  smNodes := {sm_text}
  pmNodes := {pm_text}
  sound := by
    intro smStore pmStore h
    let smNodes : List NodeDecl := {sm_text}
    let pmNodes : List NodeDecl := {pm_text}
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pmStore
    have hframe : {pre_state.state_id}.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore h
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin : {before.fact_id}.Holds smStore pmStore := h {before.fact_id} (by native_decide)
    have hsmOut : smFinal {so} = smStore {si} := by
      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed,
        applyNodeRingAttn, applyNode_fw_float_out]
    have hpm0Out : pmFinal {p0o} = pmStore {p0i} := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_eq_of_not_mem_outs]
      · exact applyNode_fw_float_out pmGraph pmStore 0 {p0i} {p0o} {params_text}
      · decide
    have hpm1Out : pmFinal {p1o} = pmStore {p1i} := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_fw_float_out]
      apply applyNode_eq_of_not_mem_outs
      decide
    have hout : {after.fact_id}.Holds smFinal pmFinal := by
      change GeneratedPatterns.Ordinary2Rel (smFinal {so}) (pmFinal {p0o}) (pmFinal {p1o}) {full_shape} {shard_shape}
      change GeneratedPatterns.Ordinary2Rel (smStore {si}) (pmStore {p0i}) (pmStore {p1i}) {full_shape} {shard_shape} at hin
      rw [hsmOut, hpm0Out, hpm1Out]
      exact hin
    exact RelationState.Holds.mono_insert hframe hout (by native_decide)
'''


def render_closed_multiref_segment(ir: GoalIR, relation, segment_id: str) -> str:
    chain=relation.dependent_chain_plan
    if chain is None or not chain.complete: raise ValueError("multiref requires complete chain")
    segment=next((x for x in chain.segments if x.segment_id==segment_id),None)
    if segment is None: raise ValueError(f"unknown segment: {segment_id}")
    by_id={x.transition_id:x for x in relation.transition_specs};transitions=[by_id[x] for x in segment.transition_ids]
    theorem="TrainVerify.Denote.fw_multiref_allGather0_commute_2"
    if not transitions or any(x.lean_theorem!=theorem or len(x.pre_facts)!=1 or len(x.post_facts)!=1 for x in transitions):
        raise ValueError("segment is not an all-multiref atomic component")
    groups={}
    for transition in transitions:
        key=(transition.sm_node_indices,transition.pm_node_indices)
        if len(key[0])!=1 or len(key[1])!=2: raise ValueError("multiref footprint is not 1xSM+2xPM")
        groups.setdefault(key,[]).append(transition)
    sm_slice=ir.sm_nodes[slice(*segment.sm_range)];pm_slice=ir.pm_nodes[slice(*segment.pm_range)]
    sm_text=[_node_text(x) for x in sm_slice];pm_text=[_node_text(x) for x in pm_slice]
    records={x.source:x for x in chain.relation_facts};states={x.state_id:x for x in chain.states}
    before_state,after_state=states[segment.pre_state_id],states[segment.post_state_id]
    rendered=[];fresh=[]
    for group_no,(key,items) in enumerate(sorted(groups.items())):
        si=key[0][0];p0i,p1i=key[1];sm=ir.sm_nodes[si];p0,p1=ir.pm_nodes[p0i],ir.pm_nodes[p1i]
        nodes=(sm,p0,p1);arity=len(sm.outs)
        if any(x.op!="FW_multiref" or len(x.ins)!=1 or len(x.outs)!=arity or x.params!=[arity] for x in nodes):
            raise ValueError("multiref group signature/arity mismatch")
        if (sm.rank,p0.rank,p1.rank)!=(0,0,1): raise ValueError("multiref group ranks are not ordered")
        pre_specs={x.pre_facts[0] for x in items}
        if len(pre_specs)!=1: raise ValueError("multiref group lacks unique input")
        pre=records[next(iter(pre_specs))]
        if pre.fact_id not in before_state.fact_ids: raise ValueError("multiref input is not live")
        rows=[]
        for item in items:
            post=records[item.post_facts[0]];projection=int(item.post_facts[0].step_triple[0].rsplit(":",1)[1])
            expected=(f"sm:{si}:{projection}",f"pm:{p0i}:{projection}",f"pm:{p1i}:{projection}")
            if projection>=arity or item.post_facts[0].step_triple!=expected: raise ValueError("multiref projection mismatch")
            if (post.kind,post.full_shape,post.shard_shape,post.metadata_tid)!=(pre.kind,pre.full_shape,pre.shard_shape,pre.metadata_tid):
                raise ValueError("multiref relation payload changed")
            rows.append((projection,post))
        rows.sort()
        if len({x for x,_ in rows})!=len(rows): raise ValueError("duplicate multiref projection")
        rendered.append((group_no,si,p0i,p1i,sm,p0,p1,pre,rows));fresh.extend(post for _,post in rows)
    if len({x.fact_id for x in fresh})!=len(fresh): raise ValueError("duplicate multiref post fact")
    if not set(after_state.fact_ids)<=({x.fact_id for x in fresh}|set(before_state.fact_ids)):
        raise ValueError("multiref state introduces an unproved fact")
    lines=[f"private def {segment.segment_id}","    (smGraph pmGraph : GraphDecl) :",
      f"    ClosedDepSegmentCertificate smGraph pmGraph {before_state.state_id} {after_state.state_id} where",
      f"  smNodes := [{', '.join(sm_text)}]",f"  pmNodes := [{', '.join(pm_text)}]","  sound := by",
      "    intro smStore pmStore hstate",f"    let smNodes : List NodeDecl := [{', '.join(sm_text)}]",
      f"    let pmNodes : List NodeDecl := [{', '.join(pm_text)}]",
      "    let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph) smStore",
      "    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pmStore",
      f"    have hframe : {before_state.state_id}.Holds smFinal pmFinal := by",
      "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
      "      · native_decide","      · native_decide","      · native_decide","      · native_decide"]
    for g,si,p0i,p1i,sm,p0,p1,pre,rows in rendered:
        lines += [f"    have hin_g{g} : {pre.fact_id}.Holds smStore pmStore := hstate {pre.fact_id} (by native_decide)"]
        side_data=[("s",sm_slice,si-segment.sm_range[0],"smGraph","smStore",sm),
                   ("p0",pm_slice,p0i-segment.pm_range[0],"pmGraph","pmStore",p0),
                   ("p1",pm_slice,p1i-segment.pm_range[0],"pmGraph","pmStore",p1)]
        for projection,post in rows:
            eqnames=[]
            for label,whole,pos,graph,store,node in side_data:
                prefix=whole[:pos];suffix=whole[pos+1:];name=f"h_{label}_g{g}_o{projection}";eqnames.append(name)
                lines += [f"    have {name} : {'smFinal' if label=='s' else 'pmFinal'} {node.outs[projection]} = {store} {node.ins[0]} := by",
                  f"      simpa [{'smFinal, smNodes' if label=='s' else 'pmFinal, pmNodes'}] using",
                  f"        (foldl_faithful_multiref_middle_writer {graph} {store}",
                  f"          [{', '.join(_node_text(x) for x in prefix)}] [{', '.join(_node_text(x) for x in suffix)}]",
                  f"          {node.rank} {node.ins[0]} {_shape_text(node.outs)} {arity} {node.outs[projection]}",
                  "          rfl (by decide) (by native_decide) (by native_decide)",
                  "          (by native_decide) (by native_decide))"]
            fs,ss=_shape_text(post.full_shape),_shape_text(post.shard_shape)
            lines += [f"    have hout_g{g}_o{projection} : {post.fact_id}.Holds smFinal pmFinal := by"]
            if post.kind=="ordinary":
                lines += [f"      change GeneratedPatterns.Ordinary2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) {fs} {ss} at hin_g{g}",
                  f"      change GeneratedPatterns.Ordinary2Rel (smFinal {sm.outs[projection]}) (pmFinal {p0.outs[projection]}) (pmFinal {p1.outs[projection]}) {fs} {ss}",
                  f"      rw [{', '.join(eqnames)}]","      exact hin_g"+str(g)]
            else:
                m=post.metadata_tid
                lines += [f"      have hmeta_g{g}_o{projection} : pmFinal {m} = pmStore {m} := by",
                  "        exact foldl_applyNodeDistributedFaithful_at_not_written pmGraph pmNodes pmStore _ (by native_decide) (by native_decide)",
                  f"      change GeneratedPatterns.Zigzag2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) (pmStore {m}) {fs} {ss} at hin_g{g}",
                  f"      change GeneratedPatterns.Zigzag2Rel (smFinal {sm.outs[projection]}) (pmFinal {p0.outs[projection]}) (pmFinal {p1.outs[projection]}) (pmFinal {m}) {fs} {ss}",
                  f"      rw [{', '.join(eqnames)}, hmeta_g{g}_o{projection}]","      exact hin_g"+str(g)]
    fresh_names=[f"hout_g{g}_o{i}" for g,_,_,_,_,_,_,_,rows in rendered for i,_ in rows]
    fresh_defs=[post.fact_id for _,_,_,_,_,_,_,_,rows in rendered for _,post in rows]
    lines += ["    intro fact hfact",f"    have covered : fact ∈ [{', '.join(fresh_defs)}] ++ {before_state.state_id}.facts := by",
      f"      exact (show {after_state.state_id}.facts ⊆ [{', '.join(fresh_defs)}] ++ {before_state.state_id}.facts by native_decide) hfact",
      "    simp only [List.mem_append] at covered",
      "    rcases covered with fresh | hold",
      "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
      "      rcases fresh with " + " | ".join(["rfl"]*len(fresh_names))]
    lines += [f"      · exact {name}" for name in fresh_names]
    lines += ["    · exact hframe fact hold",""]
    return "\n".join(lines)

def render_closed_binary_segment(ir: GoalIR, relation, segment_id: str) -> str:
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("binary renderer requires complete closed chain")
    segment = next((x for x in chain.segments if x.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("binary renderer requires one atomic transition")
    transition = {x.transition_id: x for x in relation.transition_specs}[segment.transition_ids[0]]
    specs = {
        "TrainVerify.Denote.GeneratedPatterns.elemwiseAdd_allGather0_commute_cp2":
            ("ordinary", "FW_add", "elemwiseAdd", "applyNode_fw_add2_out", "add"),
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.add":
            ("zigzag", "FW_add", "elemwiseAdd", "applyNode_fw_add2_out", "add"),
        "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.mul_broadcast_col1":
            ("ordinary", "FW_mul", "elemwiseMul", "applyNode_fw_mul_out", "mul_broadcast"),
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.mul_broadcast_col1":
            ("zigzag", "FW_mul", "elemwiseMul", "applyNode_fw_mul_out", "mul_broadcast"),
    }
    spec = specs.get(transition.lean_theorem)
    if spec is None or len(transition.pre_facts) != 2 or len(transition.post_facts) != 1:
        raise ValueError("binary renderer received unsupported transition")
    expected_kind, expected_op, tensor_op, apply_lemma, family = spec
    records = {x.source: x for x in chain.relation_facts}
    pre_records = [records[x] for x in transition.pre_facts]
    post = records[transition.post_facts[0]]
    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    if len(sm_nodes) != 1 or len(pm_nodes) != 2:
        raise ValueError("binary footprint is not 1xSM+2xPM")
    sm, p0, p1 = sm_nodes[0], pm_nodes[0], pm_nodes[1]
    by_sm_tid = {x.sm_tid: x for x in pre_records}
    if len(by_sm_tid) != 2 or any(tid not in by_sm_tid for tid in sm.ins):
        raise ValueError("binary inputs lack unique role-preserving SM facts")
    # SM defines semantic operand roles.  Relation planning aligns each PM input
    # to these roles, so graph operand order (including commutative swaps) cannot
    # silently exchange the gate and payload facts.
    a, b = (by_sm_tid[tid] for tid in sm.ins)
    if not (a.kind == b.kind == post.kind == expected_kind):
        raise ValueError("binary relation kinds disagree")
    if family == "add":
        if (a.full_shape, a.shard_shape) != (b.full_shape, b.shard_shape) or (a.full_shape, a.shard_shape) != (post.full_shape, post.shard_shape):
            raise ValueError("binary add shapes disagree")
    else:
        if len(a.full_shape) != 2 or len(b.full_shape) != 2:
            raise ValueError("broadcast mul inputs are not rank-2")
        if a.full_shape != (b.full_shape[0], 1) or a.shard_shape != (b.shard_shape[0], 1):
            raise ValueError("broadcast mul gate is not col1")
        if (b.full_shape, b.shard_shape) != (post.full_shape, post.shard_shape):
            raise ValueError("broadcast mul payload/output shapes disagree")
    if len(post.full_shape) != 2 or post.full_shape[0] != 2 * post.shard_shape[0] or post.full_shape[1] != post.shard_shape[1]:
        raise ValueError("binary result is not dim-0 CP2")
    if post.kind == "zigzag":
        metadata = {(x.metadata_tid, x.metadata_region_id) for x in (a, b, post)}
        if len(metadata) != 1 or post.metadata_tid is None:
            raise ValueError("binary zigzag inputs do not share metadata")
    if any(n.op != expected_op or len(n.ins) != 2 or len(n.outs) != 1 or n.params for n in (sm, p0, p1)):
        raise ValueError("binary node signature mismatch")
    if (sm.rank, p0.rank, p1.rank) != (0, 0, 1):
        raise ValueError("binary ranks mismatch")
    expected_inputs = ((a.sm_tid, b.sm_tid), (a.pm_rank0_tid, b.pm_rank0_tid), (a.pm_rank1_tid, b.pm_rank1_tid))
    if tuple(tuple(n.ins) for n in (sm, p0, p1)) != expected_inputs:
        raise ValueError("binary inputs mismatch")
    if (sm.outs[0], p0.outs[0], p1.outs[0]) != (post.sm_tid, post.pm_rank0_tid, post.pm_rank1_tid):
        raise ValueError("binary outputs mismatch")
    states = {x.state_id: x for x in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if not {a.fact_id, b.fact_id} <= set(before.fact_ids) or post.fact_id not in after.fact_ids:
        raise ValueError("binary facts not live")
    if not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("binary post-state introduces facts")
    smt = _node_text(sm); pmt = [_node_text(p0), _node_text(p1)]
    full = _shape_text(list(post.full_shape)); shard = _shape_text(list(post.shard_shape)); ldim, d = post.shard_shape
    a_full = _shape_text(list(a.full_shape)); a_shard = _shape_text(list(a.shard_shape))
    b_full = _shape_text(list(b.full_shape)); b_shard = _shape_text(list(b.shard_shape))

    def output(name, graph, store, nodes, pos, node, final):
        bef, aft = nodes[:pos], nodes[pos + 1:]
        return [f"    have {name} : {final} {node.outs[0]} = {tensor_op} ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",
          f"      simpa [{final}, {'smNodes' if final == 'smFinal' else 'pmNodes'}] using",
          f"        (foldl_faithful_binary_middle_writer {graph} {store} [{', '.join(_node_text(x) for x in bef)}] [{', '.join(_node_text(x) for x in aft)}] {_node_text(node)}",
          f"          {node.ins[0]} {node.ins[1]} {node.outs[0]} {tensor_op} (by",
          "            intro t", "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
          "              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]", "            simp [applyNodeDistributed, applyNodeRingAttn]",
          f"            exact {apply_lemma} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]})",
          "          (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))"]

    lines = [f"private def {segment.segment_id} (smGraph pmGraph : GraphDecl) :", f"    ClosedDepSegmentCertificate smGraph pmGraph {before.state_id} {after.state_id} where",
      f"  smNodes := [{smt}]", f"  pmNodes := [{', '.join(pmt)}]", "  sound := by", "    intro smStore pmStore hstate", f"    let smNodes : List NodeDecl := [{smt}]", f"    let pmNodes : List NodeDecl := [{', '.join(pmt)}]",
      "    let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph) smStore", "    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pmStore",
      f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by", "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate", "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
      f"    have ha : {a.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)", f"    have hb : {b.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)"]
    lines += output("hsm", "smGraph", "smStore", sm_nodes, 0, sm, "smFinal")
    lines += output("hp0", "pmGraph", "pmStore", pm_nodes, 0, p0, "pmFinal")
    lines += output("hp1", "pmGraph", "pmStore", pm_nodes, 1, p1, "pmFinal")
    relation_name = "GeneratedPatterns.Ordinary2Rel" if post.kind == "ordinary" else "GeneratedPatterns.Zigzag2Rel"
    meta_final = "" if post.kind == "ordinary" else f" (pmFinal {post.metadata_tid})"
    meta_a = "" if post.kind == "ordinary" else f" (pmStore {a.metadata_tid})"
    meta_b = "" if post.kind == "ordinary" else f" (pmStore {b.metadata_tid})"
    theorem = (
        "Ordinary2Rel.add" if family == "add" and post.kind == "ordinary" else
        "GeneratedPatterns.Zigzag2Rel.add" if family == "add" else
        "Ordinary2Rel.mul_broadcast_col1" if post.kind == "ordinary" else
        "GeneratedPatterns.Zigzag2Rel.mul_broadcast_col1"
    )
    lines += [f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
      f"      change {relation_name} (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}){meta_final} {full} {shard}",
      f"      change {relation_name} (smStore {a.sm_tid}) (pmStore {a.pm_rank0_tid}) (pmStore {a.pm_rank1_tid}){meta_a} {a_full} {a_shard} at ha",
      f"      change {relation_name} (smStore {b.sm_tid}) (pmStore {b.pm_rank0_tid}) (pmStore {b.pm_rank1_tid}){meta_b} {b_full} {b_shard} at hb"]
    if post.kind == "zigzag":
        lines += [f"      have hmeta : pmFinal {post.metadata_tid} = pmStore {post.metadata_tid} := foldl_applyNodeDistributedFaithful_at_not_written pmGraph pmNodes pmStore {post.metadata_tid} (by native_decide) (by native_decide)", "      rw [hsm, hp0, hp1, hmeta]"]
    else:
        lines += ["      rw [hsm, hp0, hp1]"]
    lines += [f"      exact {theorem} {ldim} {d} ha hb (by decide) (by decide)",
      "    exact RelationState.Holds.mono_insert hframe hout (by native_decide)", ""]
    return "\n".join(lines)


def render_closed_unary_segment(ir: GoalIR, relation, segment_id: str) -> str:
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("unary renderer requires a complete closed chain")
    segment = next((x for x in chain.segments if x.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("unary renderer requires one atomic transition")
    transition = {x.transition_id: x for x in relation.transition_specs}[segment.transition_ids[0]]
    identity_theorems = {
        "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id",
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_id",
        "TrainVerify.Denote.fw_float_allGather0_commute_2",
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.fw_float",
    }
    if transition.lean_theorem not in identity_theorems:
        raise ValueError("unary renderer received unsupported theorem")
    if len(transition.pre_facts) != 1 or len(transition.post_facts) != 1:
        raise ValueError("unary identity requires one pre/post fact")
    facts = {x.source: x for x in chain.relation_facts}
    pre, post = facts[transition.pre_facts[0]], facts[transition.post_facts[0]]
    if pre.kind != post.kind or pre.kind not in ("ordinary", "zigzag"):
        raise ValueError("unary identity relation kind mismatch")
    if (pre.full_shape, pre.shard_shape) != (post.full_shape, post.shard_shape):
        raise ValueError("identity unary changes relation shape")
    if pre.kind == "zigzag" and (
        pre.metadata_tid is None or pre.metadata_tid != post.metadata_tid or
        pre.metadata_region_id != post.metadata_region_id
    ):
        raise ValueError("identity unary changes metadata provenance")
    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    if len(sm_nodes) != 1 or len(pm_nodes) != 2:
        raise ValueError("unary identity footprint is not 1xSM+2xPM")
    sm, p0, p1 = sm_nodes[0], pm_nodes[0], pm_nodes[1]
    if sm.op not in ("FW_view", "FW_reshape", "FW_float") or any(n.op != sm.op for n in (p0, p1)):
        raise ValueError("identity unary operator mismatch")
    if (sm.rank, p0.rank, p1.rank) != (0, 0, 1):
        raise ValueError("identity unary ranks are not ordered")
    if any(len(n.ins) != 1 or len(n.outs) != 1 for n in (sm, p0, p1)):
        raise ValueError("identity unary arity mismatch")
    if sm.op == "FW_float":
        if any(n.params for n in (sm, p0, p1)):
            raise ValueError("FW_float must have empty params")
    elif any(not n.params for n in (sm, p0, p1)) or tuple(sm.params) != pre.full_shape or tuple(p0.params) != pre.shard_shape or tuple(p1.params) != pre.shard_shape:
        raise ValueError("identity unary target shapes mismatch")
    if (sm.ins[0], p0.ins[0], p1.ins[0]) != (pre.sm_tid, pre.pm_rank0_tid, pre.pm_rank1_tid):
        raise ValueError("identity unary inputs mismatch")
    if (sm.outs[0], p0.outs[0], p1.outs[0]) != (post.sm_tid, post.pm_rank0_tid, post.pm_rank1_tid):
        raise ValueError("identity unary outputs mismatch")
    states = {x.state_id: x for x in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if pre.fact_id not in before.fact_ids or post.fact_id not in after.fact_ids:
        raise ValueError("identity unary fact is not live")
    if not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("identity unary introduces unproved state")
    sm_text = _node_text(sm); pm_text = [_node_text(p0), _node_text(p1)]
    full_shape = _shape_text(list(pre.full_shape)); shard_shape = _shape_text(list(pre.shard_shape))

    def app(node: Node, graph: str, indent: str):
        params = list(node.params or ())
        lines = [indent + "intro t",
            indent + "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            indent + "  (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            indent + "simp [applyNodeDistributed, applyNodeRingAttn]"]
        if node.op == "FW_view":
            lines += [indent + f"exact applyNode_fw_view_out {graph} t {node.rank} {params[0]} {_shape_text(params[1:])} {node.ins[0]} {node.outs[0]}"]
        elif node.op == "FW_reshape":
            lines += [indent + f"exact applyNode_fw_reshape_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]} {_shape_text(params)}"]
        else:
            lines += [indent + f"exact applyNode_fw_float_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]} []"]
        return lines

    def out(name: str, graph: str, store: str, nodes: list[Node], pos: int, node: Node, final: str, shape: tuple[int, ...]):
        prior, later = nodes[:pos], nodes[pos+1:]
        rhs = f"fw_view {_shape_text(list(shape))} ({store} {node.ins[0]})" if node.op != "FW_float" else f"{store} {node.ins[0]}"
        fn = f"fun x => fw_view {_shape_text(list(shape))} x" if node.op != "FW_float" else "fun x => x"
        lines = [f"    have {name} : {final} {node.outs[0]} = {rhs} := by",
            f"      simpa [{final}, {'smNodes' if final == 'smFinal' else 'pmNodes'}] using",
            f"        (foldl_faithful_unary_middle_writer {graph} {store}",
            f"          [{', '.join(_node_text(x) for x in prior)}] [{', '.join(_node_text(x) for x in later)}] {_node_text(node)}",
            f"          {node.ins[0]} {node.outs[0]} ({fn}) (by"]
        lines += app(node, graph, "            ")
        lines += ["          ) (by native_decide) (by native_decide) (by native_decide) (by native_decide))"]
        return lines

    lines = [f"private def {segment.segment_id} (smGraph pmGraph : GraphDecl) :",
        f"    ClosedDepSegmentCertificate smGraph pmGraph {before.state_id} {after.state_id} where",
        f"  smNodes := [{sm_text}]", f"  pmNodes := [{', '.join(pm_text)}]", "  sound := by",
        "    intro smStore pmStore hstate", f"    let smNodes : List NodeDecl := [{sm_text}]",
        f"    let pmNodes : List NodeDecl := [{', '.join(pm_text)}]",
        "    let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph) smStore",
        "    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hin : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)"]
    lines += out("hsm", "smGraph", "smStore", sm_nodes, 0, sm, "smFinal", pre.full_shape)
    lines += out("hp0", "pmGraph", "pmStore", pm_nodes, 0, p0, "pmFinal", pre.shard_shape)
    lines += out("hp1", "pmGraph", "pmStore", pm_nodes, 1, p1, "pmFinal", pre.shard_shape)
    if pre.kind == "ordinary":
        lines += [f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change GeneratedPatterns.Ordinary2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) {full_shape} {shard_shape}",
            f"      change GeneratedPatterns.Ordinary2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) {full_shape} {shard_shape} at hin",
            "      rw [hsm, hp0, hp1]",
            "      exact hin" if sm.op == "FW_float" else "      exact Ordinary2Rel.view_id hin"]
    else:
        lines += [f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change GeneratedPatterns.Zigzag2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) (pmFinal {post.metadata_tid}) {full_shape} {shard_shape}",
            f"      change GeneratedPatterns.Zigzag2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) (pmStore {pre.metadata_tid}) {full_shape} {shard_shape} at hin",
            f"      have hmeta : pmFinal {post.metadata_tid} = pmStore {pre.metadata_tid} := by",
            f"        exact foldl_applyNodeDistributedFaithful_at_not_written pmGraph pmNodes pmStore {pre.metadata_tid} (by native_decide) (by native_decide)",
            "      rw [hsm, hp0, hp1, hmeta]",
            "      have hcore := GeneratedPatterns.Zigzag2Rel.fw_float 2 0 0 1 [] hin" if sm.op == "FW_float" else "      exact GeneratedPatterns.Zigzag2Rel.view_id' hin"]
        if pre.kind == "zigzag" and sm.op == "FW_float":
            lines += ["      simpa only [evalOp_fw_float, List.headD_cons] using hcore"]
    lines += ["    exact RelationState.Holds.mono_insert hframe hout (by native_decide)", ""]
    return "\n".join(lines)


def render_closed_linear_segment(ir: GoalIR, relation, segment_id: str) -> str:
    from .relation_compiler import (
        FrontierLinearCertificate, FullProducerChunkCertificate,
        PerHeadLinearRelationCertificate,
    )
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("linear renderer requires complete closed chain")
    segment = next((x for x in chain.segments if x.segment_id == segment_id), None)
    if segment is None:
        raise ValueError(f"unknown linear segment: {segment_id}")
    by_id = {x.transition_id: x for x in relation.transition_specs}
    transitions = [by_id[x] for x in segment.transition_ids]
    allowed = {
        "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.per_head_linear_fullProducer_chunks",
        "TrainVerify.Denote.fw_per_head_mix_precision_linear_allGather0_commute_2",
        "TrainVerify.Denote.fw_mix_precision_linear_allGather0_commute_2",
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.mix_precision_linear",
    }
    if not transitions or any(x.lean_theorem not in allowed for x in transitions):
        raise ValueError("linear renderer received an unsupported linear component")
    records = {x.source: x for x in chain.relation_facts}
    states = {x.state_id: x for x in chain.states}
    pre_state, post_state = states[segment.pre_state_id], states[segment.post_state_id]
    sm_slice = ir.sm_nodes[slice(*segment.sm_range)]
    pm_slice = ir.pm_nodes[slice(*segment.pm_range)]
    sm_start, pm_start = segment.sm_range[0], segment.pm_range[0]
    sm_text = [_node_text(x) for x in sm_slice]
    pm_text = [_node_text(x) for x in pm_slice]
    authority = {x.fact_id: x for x in chain.authority_facts}
    live_authority = [authority[x] for x in pre_state.fact_ids if x in authority]

    def weight_facts(tid: int, expected_shape: tuple[int, ...]):
        eqs = [x for x in live_authority if x.kind == "tensor_eq" and
               (x.left_side, x.left_tid, x.right_side, x.right_tid) == ("sm", tid, "pm", tid)]
        shapes = [x for x in live_authority if x.kind == "tensor_shape" and
                  (x.side, x.tid, x.shape) == ("pm", tid, expected_shape)]
        if len(eqs) != 1 or len(shapes) != 1:
            raise ValueError(f"linear weight lacks unique live equality/shape authority: {tid}")
        return eqs[0], shapes[0]

    def apply_lines(graph: str, node: Node, op: str, indent: str):
        if node.params:
            raise ValueError("linear node has nonempty params")
        if op == "FW_per_head_mix_precision_linear":
            conclusion = f"exact applyNode_fw_per_head_mix_precision_linear_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]} []"
        elif op == "FW_mix_precision_linear":
            conclusion = f"exact applyNode_fw_mix_precision_linear_out_1p {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}"
        else:
            raise ValueError(f"unsupported linear operator: {op}")
        return [
            indent + "intro t",
            indent + "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            indent + "  (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            indent + "simp [applyNodeDistributed, applyNodeRingAttn]",
            indent + conclusion,
        ]

    def binary_middle(name: str, graph: str, store: str, nodes: list[Node], pos: int, node: Node,
                      final: str, expr: str):
        before, after = nodes[:pos], nodes[pos + 1:]
        result = [
            f"    have {name} : {final} {node.outs[0]} = {expr.format(x=f'({store} {node.ins[0]})', w=f'({store} {node.ins[1]})')} := by",
            f"      simpa [{final}, {'smNodes' if final == 'smFinal' else 'pmNodes'}] using",
            f"        (foldl_faithful_binary_middle_writer {graph} {store}",
            f"          [{', '.join(_node_text(x) for x in before)}] [{', '.join(_node_text(x) for x in after)}] {_node_text(node)}",
            f"          {node.ins[0]} {node.ins[1]} {node.outs[0]} (fun x w => {expr.format(x='x', w='w')}) (by",
        ]
        result += apply_lines(graph, node, node.op, "            ")
        result += ["          ) (by native_decide) (by native_decide) (by native_decide)",
                   "          (by native_decide) (by native_decide))"]
        return result

    lines = [
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {pre_state.state_id} {post_state.state_id} where",
        f"  smNodes := [{', '.join(sm_text)}]",
        f"  pmNodes := [{', '.join(pm_text)}]",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := [{', '.join(sm_text)}]",
        f"    let pmNodes : List NodeDecl := [{', '.join(pm_text)}]",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hframe : {pre_state.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
    ]
    fresh = []
    certs = [x for x in relation.certificates if type(x) in (
        FrontierLinearCertificate, FullProducerChunkCertificate,
        PerHeadLinearRelationCertificate,
    )]
    for number, transition in enumerate(transitions):
        if len(transition.pre_facts) != 1 or len(transition.post_facts) != 1:
            raise ValueError("linear transition must have one pre/post fact")
        pre, post = records[transition.pre_facts[0]], records[transition.post_facts[0]]
        if pre.kind != post.kind or pre.kind not in ("ordinary", "zigzag"):
            raise ValueError("linear relation kind changes unexpectedly")
        if pre.kind == "zigzag" and (
            pre.metadata_tid != post.metadata_tid or
            pre.metadata_region_id != post.metadata_region_id or
            pre.metadata_tid is None
        ):
            raise ValueError("zigzag linear metadata provenance mismatch")
        fresh.append(post)
        cert_matches = [c for c in certs if getattr(c, "output_step_triple", None) == post.source.step_triple]
        if len(cert_matches) != 1:
            raise ValueError("linear transition lacks unique exact certificate")
        cert = cert_matches[0]
        sm_idx = transition.sm_node_indices[0]
        sm = ir.sm_nodes[sm_idx]
        if len(sm.ins) != 2 or len(sm.outs) != 1 or sm.params:
            raise ValueError("SM linear signature mismatch")
        weight_tid = sm.ins[1]
        if type(cert) is FrontierLinearCertificate:
            if sm.op != "FW_mix_precision_linear" or len(transition.pm_node_indices) != 2:
                raise ValueError("ordinary mix linear footprint mismatch")
            p0i, p1i = transition.pm_node_indices
            p0, p1 = ir.pm_nodes[p0i], ir.pm_nodes[p1i]
            if any(n.op != sm.op or n.params or len(n.ins) != 2 or len(n.outs) != 1 for n in (p0, p1)):
                raise ValueError("PM mix linear signature mismatch")
            if (p0.rank, p1.rank) != (0, 1) or p0.ins[1] != weight_tid or p1.ins[1] != weight_tid:
                raise ValueError("PM mix linear rank/weight mismatch")
            if len(pre.full_shape) != 2 or len(post.full_shape) != 2:
                raise ValueError("mix linear shape rank mismatch")
            ldim, in_dim = pre.shard_shape
            out_dim = post.shard_shape[1]
            if pre.full_shape != (ldim * 2, in_dim) or post.full_shape != (ldim * 2, out_dim) or post.shard_shape != (ldim, out_dim):
                raise ValueError("mix linear shape mismatch")
            weight_shape = (out_dim, in_dim)
            eq, shape = weight_facts(weight_tid, weight_shape)
            lines += [
                f"    have hin{number} : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
                f"    have hwEq{number} : {eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
                f"    have hwShape{number} : {shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            ]
            lines += binary_middle(f"hSm{number}", ir.sm_graph_ref, "smStore", sm_slice, sm_idx - sm_start, sm, "smFinal", "fw_linear {x} {w}")
            lines += binary_middle(f"hPm{number}_0", ir.pm_graph_ref, "pmStore", pm_slice, p0i - pm_start, p0, "pmFinal", "fw_linear {x} {w}")
            lines += binary_middle(f"hPm{number}_1", ir.pm_graph_ref, "pmStore", pm_slice, p1i - pm_start, p1, "pmFinal", "fw_linear {x} {w}")
            if pre.kind == "ordinary":
                lines += [
                    f"    have hout{number} : {post.fact_id}.Holds smFinal pmFinal := by",
                    f"      change GeneratedPatterns.Ordinary2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
                    f"      change GeneratedPatterns.Ordinary2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))} at hin{number}",
                    f"      change smStore {weight_tid} = pmStore {weight_tid} at hwEq{number}",
                    f"      change (pmStore {weight_tid}).shape = {_shape_text(list(weight_shape))} at hwShape{number}",
                    f"      rw [hSm{number}, hPm{number}_0, hPm{number}_1]",
                    f"      exact Ordinary2Rel.mix_precision_linear {ldim} {in_dim} {out_dim} hin{number} hwShape{number} hwEq{number}",
                    "        (by decide) (by decide) (by decide)",
                ]
            else:
                lines += [
                    f"    have hout{number} : {post.fact_id}.Holds smFinal pmFinal := by",
                    f"      change GeneratedPatterns.Zigzag2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) (pmFinal {post.metadata_tid}) {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
                    f"      change GeneratedPatterns.Zigzag2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) (pmStore {pre.metadata_tid}) {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))} at hin{number}",
                    f"      change smStore {weight_tid} = pmStore {weight_tid} at hwEq{number}",
                    f"      change (pmStore {weight_tid}).shape = {_shape_text(list(weight_shape))} at hwShape{number}",
                    f"      rw [hSm{number}, hPm{number}_0, hPm{number}_1, hwEq{number}]",
                    f"      exact GeneratedPatterns.Zigzag2Rel.mix_precision_linear {ldim} {in_dim} {out_dim} hin{number} hwShape{number}",
                    "        (by decide) (by decide) (by decide)",
                ]
            continue
        if sm.op != "FW_per_head_mix_precision_linear":
            raise ValueError("SM per-head linear operator mismatch")
        if tuple(post.full_shape[:1]) != (pre.full_shape[0],) or len(pre.full_shape) != 2 or len(post.full_shape) != 3:
            raise ValueError("per-head linear shape rank mismatch")
        ldim, k = pre.shard_shape
        if pre.full_shape != (ldim * 2, k) or post.full_shape[0] != ldim * 2 or post.shard_shape[0] != ldim:
            raise ValueError("per-head linear dim-0 shape mismatch")
        hdim, ddim = post.shard_shape[1:]
        weight_shape = (hdim, ddim, k)
        eq, shape = weight_facts(weight_tid, weight_shape)
        if eq.fact_id not in pre_state.fact_ids or shape.fact_id not in pre_state.fact_ids:
            raise ValueError("linear weight authority is not live")
        lines += [
            f"    have hin{number} : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"    have hwEq{number} : {eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"    have hwShape{number} : {shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        ]
        lines += binary_middle(f"hSm{number}", ir.sm_graph_ref, "smStore", sm_slice,
                               sm_idx - sm_start, sm, "smFinal", "fw_per_head_linear {x} {w}")
        if type(cert) is PerHeadLinearRelationCertificate:
            if len(transition.pm_node_indices) != 2:
                raise ValueError("local per-head linear footprint is not 1x2")
            p0i, p1i = transition.pm_node_indices
            p0, p1 = ir.pm_nodes[p0i], ir.pm_nodes[p1i]
            if (p0.rank, p1.rank) != (0, 1) or any(n.ins[1] != weight_tid for n in (p0, p1)):
                raise ValueError("local PM per-head linear weight/ranks mismatch")
            lines += binary_middle(f"hPm{number}_0", ir.pm_graph_ref, "pmStore", pm_slice,
                                   p0i - pm_start, p0, "pmFinal", "fw_per_head_linear {x} {w}")
            lines += binary_middle(f"hPm{number}_1", ir.pm_graph_ref, "pmStore", pm_slice,
                                   p1i - pm_start, p1, "pmFinal", "fw_per_head_linear {x} {w}")
            lines += [
                f"    have hout{number} : {post.fact_id}.Holds smFinal pmFinal := by",
                f"      change GeneratedPatterns.Ordinary2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
                f"      change GeneratedPatterns.Ordinary2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))} at hin{number}",
                f"      change smStore {weight_tid} = pmStore {weight_tid} at hwEq{number}",
                f"      change (pmStore {weight_tid}).shape = {_shape_text(list(weight_shape))} at hwShape{number}",
                f"      rw [hSm{number}, hPm{number}_0, hPm{number}_1]",
                f"      exact Ordinary2Rel.per_head_linear {ldim} {k} {hdim} {ddim} hin{number} hwShape{number} hwEq{number}",
                "        (by decide) (by decide) (by decide) (by decide)",
            ]
            continue
        if type(cert) is not FullProducerChunkCertificate:
            raise ValueError("unsupported exact linear certificate class")
        if cert.replicated_weight_binding != f"init:{weight_tid}" or cert.weight_init_lineage_rank_tids != ((0, weight_tid),):
            raise ValueError("full-producer weight lineage mismatch")
        if len(transition.pm_node_indices) != 4:
            raise ValueError("full-producer footprint must contain gather, producer, two chunks")
        gi, pi, c0i, c1i = transition.pm_node_indices
        gather, producer, c0, c1 = (ir.pm_nodes[i] for i in (gi, pi, c0i, c1i))
        if gather.op != "AllGatherPrim" or gather.params != [0] or len(gather.ins) != 2 or gather.rank != 0:
            raise ValueError("full-producer gather signature mismatch")
        if producer.op != sm.op or producer.ins != [gather.outs[0], weight_tid] or producer.outs != sm.outs:
            raise ValueError("full-producer node mismatch")
        if (c0.op, c1.op, c0.rank, c1.rank, c0.params, c1.params) != ("ChunkPrim", "ChunkPrim", 0, 1, [0], [0]):
            raise ValueError("full-producer chunk signature mismatch")
        if c0.ins != producer.outs or c1.ins != producer.outs:
            raise ValueError("chunks do not consume exact producer")
        gpos, ppos, c0pos, c1pos = (i - pm_start for i in (gi, pi, c0i, c1i))
        before_g, after_g = pm_slice[:gpos], pm_slice[gpos + 1:ppos]
        lines += [
            f"    let pmBeforeProducer{number} := [{', '.join(_node_text(x) for x in pm_slice[:ppos])}].foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
            f"    have hGather{number} : pmBeforeProducer{number} {gather.outs[0]} = allGatherPrimDimN 0 2 0 [pmStore {gather.ins[0]}, pmStore {gather.ins[1]}] := by",
            f"      simpa [pmBeforeProducer{number}] using",
            f"        (foldl_faithful_binary_middle_writer {ir.pm_graph_ref} pmStore",
            f"          [{', '.join(_node_text(x) for x in before_g)}] [{', '.join(_node_text(x) for x in after_g)}] {_node_text(gather)}",
            f"          {gather.ins[0]} {gather.ins[1]} {gather.outs[0]} (fun x y => allGatherPrimDimN 0 2 0 [x, y]) (by",
            "            intro t",
            "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "            simp [applyNodeDistributed, applyNodeRingAttn]",
            f"            rw [applyNode_allGatherPrimDimN_out {ir.pm_graph_ref} t 0 [{gather.ins[0]}, {gather.ins[1]}] {gather.outs[0]} 0]",
            f"            rw [show {ir.pm_graph_ref}.numRanks = 2 by rfl]",
            "            rfl) (by native_decide) (by native_decide) (by native_decide)",
            "          (by native_decide) (by native_decide))",
            f"    have hWeightBefore{number} : pmBeforeProducer{number} {weight_tid} = pmStore {weight_tid} := by",
            f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref}",
            f"        [{', '.join(_node_text(x) for x in pm_slice[:ppos])}] pmStore {weight_tid} (by native_decide) (by native_decide)",
        ]
        # Producer values immediately before each chunk.
        for rank, (ci, cnode, cpos) in enumerate(((c0i, c0, c0pos), (c1i, c1, c1pos))):
            producer_after = pm_slice[ppos + 1:cpos]
            lines += [
                f"    let pmBeforeChunk{number}_{rank} := [{', '.join(_node_text(x) for x in pm_slice[:cpos])}].foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
                f"    have hProducer{number}_{rank} : pmBeforeChunk{number}_{rank} {producer.outs[0]} = fw_per_head_linear (allGatherPrimDimN 0 2 0 [pmStore {gather.ins[0]}, pmStore {gather.ins[1]}]) (pmStore {weight_tid}) := by",
                f"      rw [show pmBeforeChunk{number}_{rank} {producer.outs[0]} = fw_per_head_linear (pmBeforeProducer{number} {producer.ins[0]}) (pmBeforeProducer{number} {producer.ins[1]}) by",
                f"        simpa [pmBeforeChunk{number}_{rank}, pmBeforeProducer{number}] using",
                f"          (foldl_faithful_binary_writer {ir.pm_graph_ref} pmStore",
                f"            [{', '.join(_node_text(x) for x in pm_slice[:ppos])}] [{', '.join(_node_text(x) for x in producer_after)}] {_node_text(producer)}",
                f"            {producer.ins[0]} {producer.ins[1]} {producer.outs[0]} (fun x w => fw_per_head_linear x w) (by",
            ]
            lines += apply_lines(ir.pm_graph_ref, producer, producer.op, "              ")
            lines += ["            ) (by native_decide) (by native_decide))]", f"      rw [hGather{number}, hWeightBefore{number}]",
                f"    have hChunk{number}_{rank} : pmFinal {cnode.outs[0]} = chunkPrimDimN 0 2 {rank} (pmBeforeChunk{number}_{rank} {producer.outs[0]}) := by",
                "      simpa [pmFinal, pmNodes, pmBeforeChunk" + f"{number}_{rank}" + "] using",
                f"        (foldl_faithful_chunk_writer {ir.pm_graph_ref} pmStore",
                f"          [{', '.join(_node_text(x) for x in pm_slice[:cpos])}] [{', '.join(_node_text(x) for x in pm_slice[cpos + 1:])}] {rank}",
                f"          {producer.outs[0]} {cnode.outs[0]} 0 rfl (by native_decide) (by native_decide))",
            ]
        lines += [
            f"    have hout{number} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change GeneratedPatterns.Ordinary2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
            f"      change GeneratedPatterns.Ordinary2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))} at hin{number}",
            f"      change smStore {weight_tid} = pmStore {weight_tid} at hwEq{number}",
            f"      change (pmStore {weight_tid}).shape = {_shape_text(list(weight_shape))} at hwShape{number}",
            f"      exact Ordinary2Rel.per_head_linear_fullProducer_chunks {ldim} {k} {hdim} {ddim}",
            f"        hin{number} hwShape{number} hwEq{number} hSm{number} hGather{number}",
            f"        hProducer{number}_0 hChunk{number}_0",
            f"        (calc pmFinal {c1.outs[0]} = chunkPrimDimN 0 2 1 (pmBeforeChunk{number}_1 {producer.outs[0]}) := hChunk{number}_1",
            f"          _ = chunkPrimDimN 0 2 1 (pmBeforeChunk{number}_0 {producer.outs[0]}) := congrArg (chunkPrimDimN 0 2 1) (hProducer{number}_1.trans hProducer{number}_0.symm))",
            "        (by decide) (by decide) (by decide) (by decide)",
        ]
    fresh_ids = [x.fact_id for x in fresh]
    if not set(post_state.fact_ids) <= (set(pre_state.fact_ids) | set(fresh_ids)):
        raise ValueError("linear segment post-state introduces unproved facts")
    lines += [
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {pre_state.state_id}.facts := by",
        f"      exact (show {post_state.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {pre_state.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with " + " | ".join("rfl" for _ in fresh),
    ]
    lines += [f"      · exact hout{i}" for i in range(len(fresh))]
    lines += ["    · exact hframe fact old", ""]
    return "\n".join(lines)


def render_closed_initial_component(ir: GoalIR, relation, segment_id: str) -> str:
    chain=relation.dependent_chain_plan
    if chain is None or not chain.complete: raise ValueError("initial component requires complete chain")
    if not ir.sm_graph_ref or not ir.pm_graph_ref or not ir.public_statement_module:
        raise ValueError("initial component lacks exact public graph references")
    segment=next((x for x in chain.segments if x.segment_id==segment_id),None)
    if segment is None: raise ValueError(f"unknown segment: {segment_id}")
    by_id={x.transition_id:x for x in relation.transition_specs};ts=[by_id[x] for x in segment.transition_ids]
    emb=[x for x in ts if x.rule_id=="hidden-sharded-embedding-alltoall-ordinary-two-rank"]
    init=[x for x in ts if x.rule_id=="init-lineage-full-to-two-chunks"]
    if len(emb)!=1 or len(init)==0 or len(init)+1!=len(ts): raise ValueError("initial component family mismatch")
    if ir.sm_num_ranks!=1 or ir.pm_num_ranks!=2: raise ValueError("initial component requires 1x2 topology")
    sm_nodes=ir.sm_nodes[slice(*segment.sm_range)];pm_nodes=ir.pm_nodes[slice(*segment.pm_range)]
    if len(sm_nodes)!=1 or sm_nodes[0].op!="FW_embedding": raise ValueError("initial SM slice mismatch")
    et=emb[0];eidx=et.sm_node_indices[0];pm_e0,pm_e1,a0i,a1i=et.pm_node_indices
    sm,pe0,pe1,a0,a1=ir.sm_nodes[eidx],ir.pm_nodes[pm_e0],ir.pm_nodes[pm_e1],ir.pm_nodes[a0i],ir.pm_nodes[a1i]
    if any(n.op!="FW_embedding" for n in (sm,pe0,pe1)) or any(n.op!="AllToAllPrim" for n in (a0,a1)):
        raise ValueError("embedding/AllToAll node mismatch")
    if (a0.params,a1.params)!=([1,0],[1,0]) or (a0.rank,a1.rank)!=(0,1): raise ValueError("AllToAll signature mismatch")
    records={x.source:x for x in chain.relation_facts};post_emb=records[et.post_facts[0]]
    auth=chain.authority_facts
    def eq_fact(ls,lt,rs,rt):
        xs=[x for x in auth if x.kind=="tensor_eq" and (x.left_side,x.left_tid,x.right_side,x.right_tid)==(ls,lt,rs,rt)]
        if len(xs)!=1: raise ValueError(f"non-unique tensor equality {(ls,lt,rs,rt)}")
        return xs[0]
    def shape_fact(side,tid):
        xs=[x for x in auth if x.kind=="tensor_shape" and (x.side,x.tid)==(side,tid)]
        if len(xs)!=1: raise ValueError(f"non-unique tensor shape {(side,tid)}")
        return xs[0]
    gathers=[x for x in auth if x.kind=="gather" and x.sm_tid==sm.ins[1] and (x.pm_rank0_tid,x.pm_rank1_tid)==(pe0.ins[1],pe1.ins[1])]
    if len(gathers)!=1: raise ValueError("hidden embedding gather authority mismatch")
    gather=gathers[0];ids_eq=eq_fact("sm",sm.ins[0],"pm",pe0.ins[0]);ids_shape=shape_fact("sm",sm.ins[0])
    states={x.state_id:x for x in chain.states};before,after=states[segment.pre_state_id],states[segment.post_state_id]
    required={ids_eq.fact_id,ids_shape.fact_id,gather.fact_id}
    if not required<=set(before.fact_ids): raise ValueError("embedding authority not live")
    smtxt=[_node_text(x) for x in sm_nodes];pmtxt=[_node_text(x) for x in pm_nodes]
    lines=[f"private def {segment.segment_id} :",f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
      f"  smNodes := [{', '.join(smtxt)}]",f"  pmNodes := [{', '.join(pmtxt)}]","  sound := by","    intro smStore pmStore hstate",
      f"    let smNodes : List NodeDecl := [{', '.join(smtxt)}]",f"    let pmNodes : List NodeDecl := [{', '.join(pmtxt)}]",
      f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
      f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
      f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
      "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
      "      · native_decide","      · native_decide","      · native_decide","      · native_decide"]
    # generic binary writer emitter
    def binary(name,graph,store,whole,pos,node,in0,in1,out,funtext,final):
        pre=whole[:pos];suf=whole[pos+1:]
        out_lines=[f"    have {name} : {final} {out} = {funtext.replace('$0',f'({store} {in0})').replace('$1',f'({store} {in1})')} := by",
          f"      simpa [{final}, {'smNodes' if final=='smFinal' else 'pmNodes'}] using",
          f"        (foldl_faithful_binary_middle_writer {graph} {store}",f"          [{', '.join(_node_text(x) for x in pre)}] [{', '.join(_node_text(x) for x in suf)}] {_node_text(node)}",
          f"          {in0} {in1} {out} (fun x y => {funtext.replace('$0','x').replace('$1','y')}) (by",
          "            intro t", "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
          "              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
          "            simp [applyNodeDistributed, applyNodeRingAttn]"]
        if node.op=="FW_embedding": out_lines += [f"            exact applyNode_fw_embedding_out {graph} t {node.rank} {in0} {in1} {out})"]
        else: raise ValueError("binary helper only supports embedding")
        out_lines += ["          (by native_decide) (by native_decide) (by native_decide)","          (by native_decide) (by native_decide))"]
        return out_lines
    lines += binary("hSm",ir.sm_graph_ref,"smStore",sm_nodes,0,sm,sm.ins[0],sm.ins[1],sm.outs[0],"fw_embedding $0 $1","smFinal")
    # Embedding values at AllToAll prefixes; use dedicated prefix final names.
    for upto,label in ((a0i,"28"),(a1i,"29")):
        prefix=ir.pm_nodes[segment.pm_range[0]:upto]
        lines += [f"    let pm{label} := [{', '.join(_node_text(x) for x in prefix)}].foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore"]
        for j,(idx,node) in enumerate(((pm_e0,pe0),(pm_e1,pe1))):
            lines += binary(f"hE{j}_{label}",ir.pm_graph_ref,"pmStore",prefix,idx-segment.pm_range[0],node,node.ins[0],node.ins[1],node.outs[0],"fw_embedding $0 $1",f"pm{label}")
    # AllToAll final writers; their prefix values are pm28/pm29.
    for rank,(idx,node,label) in enumerate(((a0i,a0,"28"),(a1i,a1,"29"))):
        pre=pm_nodes[:idx-segment.pm_range[0]];suf=pm_nodes[idx-segment.pm_range[0]+1:]
        lines += [f"    have hA{rank} : pmFinal {node.outs[0]} = allToAllPrimWithDims 2 {rank} [pm{label} {node.ins[0]}, pm{label} {node.ins[1]}] 1 0 := by",
          "      simpa [pmFinal, pmNodes, pm"+label+"] using",
          f"        (foldl_faithful_binary_writer {ir.pm_graph_ref} pmStore [{', '.join(_node_text(x) for x in pre)}] [{', '.join(_node_text(x) for x in suf)}] {_node_text(node)}",
          f"          {node.ins[0]} {node.ins[1]} {node.outs[0]} (fun x y => allToAllPrimWithDims 2 {rank} [x, y] 1 0) (by",
          "            intro t","            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
          "              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]","            simp [applyNodeDistributed, applyNodeRingAttn]",
          f"            rw [applyNode_allToAllPrimWithDims_out {ir.pm_graph_ref} t {rank} [{node.ins[0]}, {node.ins[1]}] {node.outs[0]} 1 0]",
          "            rfl) (by native_decide) (by native_decide))"]
    lines += [f"    have hIdsEq : {ids_eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
      f"    have hIdsShape : {ids_shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
      f"    have hWeight : {gather.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
      f"    have hout_embedding : {post_emb.fact_id}.Holds smFinal pmFinal := by",
      f"      change GeneratedPatterns.Ordinary2Rel (smFinal {sm.outs[0]}) (pmFinal {a0.outs[0]}) (pmFinal {a1.outs[0]}) {_shape_text(post_emb.full_shape)} {_shape_text(post_emb.shard_shape)}",
      "      rw [hSm, hA0, hA1, hE0_28, hE1_28, hE0_29, hE1_29]",
      f"      change smStore {sm.ins[0]} = pmStore {pe0.ins[0]} at hIdsEq",
      f"      change (smStore {sm.ins[0]}).shape = {_shape_text(ids_shape.shape)} at hIdsShape",
      f"      have hIdsShapePM : (pmStore {pe0.ins[0]}).shape = {_shape_text(ids_shape.shape)} := by rw [← hIdsEq]; exact hIdsShape",
      f"      change smStore {gather.sm_tid} = allGatherPrimDimN {gather.dim} 2 0 [pmStore {gather.pm_rank0_tid}, pmStore {gather.pm_rank1_tid}] ∧ _ at hWeight",
      f"      exact TrainVerify.Denote.RelationCompiler.Ordinary2Rel.embedding_hidden_shards_allToAll_two {post_emb.shard_shape[0]} {gather.full_shape[0]} {gather.shard_shape[1]}",
      f"        (smStore {sm.ins[0]}) (pmStore {pe0.ins[0]}) (smStore {gather.sm_tid}) (pmStore {gather.pm_rank0_tid}) (pmStore {gather.pm_rank1_tid})",
      "        (by decide) (by decide) (by decide) hIdsEq (by simpa using hIdsShapePM)",
      "        hWeight.1 hWeight.2.1 hWeight.2.2.1 hWeight.2.2.2"]
    fresh=[post_emb];
    # InitChunk outputs.
    for k,t in enumerate(init):
        post=records[t.post_facts[0]];p0i,p1i=t.pm_node_indices;p0,p1=ir.pm_nodes[p0i],ir.pm_nodes[p1i];full=int(t.post_facts[0].step_triple[0].split(':')[1]);eq=eq_fact("sm",full,"pm",p0.ins[0]);shape=shape_fact("pm",p0.ins[0])
        if post.full_shape!=(shape.shape) or len(post.full_shape)!=1 or post.full_shape[0]!=2*post.shard_shape[0]: raise ValueError("InitChunk 1D shape mismatch")
        lines += [f"    have hEq{k} : {eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",f"    have hShape{k} : {shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
          f"    have hSmInit{k} : smFinal {full} = smStore {full} := by exact foldl_applyNodeDistributedFaithful_at_not_written {ir.sm_graph_ref} smNodes smStore {full} (by native_decide) (by native_decide)"]
        for lab,idx,node in (("0",p0i,p0),("1",p1i,p1)):
            pos=idx-segment.pm_range[0];pre=pm_nodes[:pos];suf=pm_nodes[pos+1:]
            lines += [f"    have hChunk{k}_{lab} : pmFinal {node.outs[0]} = chunkPrimDimN 0 2 {node.rank} (pmStore {node.ins[0]}) := by",
              "      simpa [pmFinal, pmNodes] using",f"        (foldl_faithful_chunk_middle_writer {ir.pm_graph_ref} pmStore [{', '.join(_node_text(x) for x in pre)}] [{', '.join(_node_text(x) for x in suf)}] {node.rank} {node.ins[0]} {node.outs[0]} 0 rfl",
              "          (by native_decide) (by native_decide) (by native_decide) (by native_decide))"]
        lines += [f"    have hout_init{k} : {post.fact_id}.Holds smFinal pmFinal := by",
          f"      change GeneratedPatterns.Ordinary2Rel (smFinal {full}) (pmFinal {p0.outs[0]}) (pmFinal {p1.outs[0]}) {_shape_text(post.full_shape)} {_shape_text(post.shard_shape)}",
          f"      rw [hSmInit{k}, hChunk{k}_0, hChunk{k}_1]",f"      change smStore {full} = pmStore {p0.ins[0]} at hEq{k}",f"      change (pmStore {p0.ins[0]}).shape = {_shape_text(shape.shape)} at hShape{k}",
          f"      exact TrainVerify.Denote.RelationCompiler.Ordinary2Rel.of_eq_chunk2_dim0_1d _ _ {post.shard_shape[0]} hEq{k} (by simpa using hShape{k}) (by decide)"]
        fresh.append(post)
    if not set(after.fact_ids)<=({x.fact_id for x in fresh}|set(before.fact_ids)): raise ValueError("initial component introduces unproved fact")
    names=["hout_embedding"]+[f"hout_init{k}" for k in range(len(init))];defs=[x.fact_id for x in fresh]
    lines += ["    intro fact hfact",f"    have covered : fact ∈ [{', '.join(defs)}] ++ {before.state_id}.facts := by",f"      exact (show {after.state_id}.facts ⊆ [{', '.join(defs)}] ++ {before.state_id}.facts by native_decide) hfact","    simp only [List.mem_append] at covered","    rcases covered with fresh | hold","    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with "+" | ".join(["rfl"]*len(names))]
    lines += [f"      · exact {x}" for x in names]+["    · exact hframe fact hold",""]
    return "\n".join(lines)


def render_closed_rms_norm_segment(ir: GoalIR, relation, segment_id: str) -> str:
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("RMSNorm segment requires a complete closed chain")
    segment = next((x for x in chain.segments if x.segment_id == segment_id), None)
    by_id = {x.transition_id: x for x in relation.transition_specs}
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("RMSNorm segment must own one transition")
    transition = by_id[segment.transition_ids[0]]
    theorem_kind = {
        "TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core": "ordinary",
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.rms_norm": "zigzag",
    }.get(transition.lean_theorem)
    if theorem_kind is None:
        raise ValueError("segment is not the registered RMSNorm family")
    sms = ir.sm_nodes[slice(*segment.sm_range)]; pms = ir.pm_nodes[slice(*segment.pm_range)]
    if len(sms) != 1 or len(pms) != 2:
        raise ValueError("RMSNorm footprint mismatch")
    sm, p0, p1 = sms[0], pms[0], pms[1]
    if any(x.op != "FW_rms_norm" or len(x.ins) != 2 or len(x.outs) != 1 or x.params not in (None, []) for x in (sm, p0, p1)):
        raise ValueError("RMSNorm signature/params mismatch")
    if (sm.rank, p0.rank, p1.rank) != (0, 0, 1) or len({sm.ins[1], p0.ins[1], p1.ins[1]}) != 1:
        raise ValueError("RMSNorm replicated weight/rank mismatch")
    weight = sm.ins[1]; records = {x.source: x for x in chain.relation_facts}
    pre, post = records[transition.pre_facts[0]], records[transition.post_facts[0]]
    if pre.kind != theorem_kind or post.kind != theorem_kind or pre.full_shape != post.full_shape or pre.shard_shape != post.shard_shape:
        raise ValueError("RMSNorm relation payload mismatch")
    if len(pre.shard_shape) != 2 or pre.full_shape != (pre.shard_shape[0] * 2, pre.shard_shape[1]):
        raise ValueError("RMSNorm shape is not two-rank 2D")
    if theorem_kind == "zigzag" and (pre.metadata_tid is None or pre.metadata_tid != post.metadata_tid or pre.metadata_region_id != post.metadata_region_id):
        raise ValueError("RMSNorm zigzag metadata provenance changed")
    shard, hidden = pre.shard_shape; weight_eq = f"authority_replicated_eq_{weight}"
    if weight_eq not in {x.fact_id for x in chain.authority_facts}:
        raise ValueError("missing weight authority")
    states = {x.state_id: x for x in chain.states}; before = states[segment.pre_state_id]; after = states[segment.post_state_id]
    if pre.fact_id not in before.fact_ids or post.fact_id not in after.fact_ids:
        raise ValueError("RMSNorm pre/post facts are absent from their states")
    if not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("RMSNorm state introduces an unproved extra fact")
    if weight_eq not in before.fact_ids:
        raise ValueError("RMSNorm weight authority is not live in the pre-state")
    st, n0, n1 = _node_text(sm), _node_text(p0), _node_text(p1); fs, ss = _shape_text(post.full_shape), _shape_text(post.shard_shape)
    lines = [f"private def {segment.segment_id}", "    (smGraph pmGraph : GraphDecl) :", f"    ClosedDepSegmentCertificate smGraph pmGraph {before.state_id} {after.state_id} where",
      f"  smNodes := [{st}]", f"  pmNodes := [{n0}, {n1}]", "  sound := by", "    intro smStore pmStore hstate", f"    let smNodes : List NodeDecl := [{st}]", f"    let pmNodes : List NodeDecl := [{n0}, {n1}]",
      "    let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph) smStore", "    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pmStore",
      f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by", "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate", "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
      f"    have hin : {pre.fact_id}.Holds smStore pmStore := hstate {pre.fact_id} (by native_decide)", f"    have hweight : {weight_eq}.Holds smStore pmStore := hstate {weight_eq} (by native_decide)", f"    change smStore {weight} = pmStore {weight} at hweight",
      f"    have hsmOut : smFinal {sm.outs[0]} = fw_rms_norm (smStore {sm.ins[0]}) (smStore {weight}) := by", "      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]", f"      exact applyNode_fw_rms_norm_out_1p smGraph smStore 0 {sm.ins[0]} {weight} {sm.outs[0]}",
      f"    have hpm0Out : pmFinal {p0.outs[0]} = fw_rms_norm (pmStore {p0.ins[0]}) (pmStore {weight}) := by", "      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]", "      rw [applyNode_eq_of_not_mem_outs]", f"      · exact applyNode_fw_rms_norm_out_1p pmGraph pmStore 0 {p0.ins[0]} {weight} {p0.outs[0]}", "      · decide",
      f"    have hpm1Out : pmFinal {p1.outs[0]} = fw_rms_norm (pmStore {p1.ins[0]}) (pmStore {weight}) := by", "      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]", "      rw [applyNode_fw_rms_norm_out_1p]", "      rw [applyNode_eq_of_not_mem_outs, applyNode_eq_of_not_mem_outs] <;> decide"]
    if theorem_kind == "ordinary":
        lines += [f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by", f"      change GeneratedPatterns.Ordinary2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) {fs} {ss} at hin", f"      have core := GeneratedPatterns.Ordinary2Rel.rms_norm_2d hin hweight (by decide : 0 < {shard}) (by decide : 0 < {hidden})", f"      change GeneratedPatterns.Ordinary2Rel (smFinal {sm.outs[0]}) (pmFinal {p0.outs[0]}) (pmFinal {p1.outs[0]}) {fs} {ss}", "      rw [hsmOut, hpm0Out, hpm1Out]", "      exact core"]
    else:
        lines += [f"    have hmeta : pmFinal {post.metadata_tid} = pmStore {post.metadata_tid} := foldl_applyNodeDistributedFaithful_at_not_written pmGraph pmNodes pmStore {post.metadata_tid} (by native_decide) (by native_decide)",
          f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by", f"      change GeneratedPatterns.Zigzag2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) (pmStore {pre.metadata_tid}) {fs} {ss} at hin", f"      change GeneratedPatterns.Zigzag2Rel (smFinal {sm.outs[0]}) (pmFinal {p0.outs[0]}) (pmFinal {p1.outs[0]}) (pmFinal {post.metadata_tid}) {fs} {ss}", "      rw [hsmOut, hpm0Out, hpm1Out, hmeta, hweight]", f"      exact GeneratedPatterns.Zigzag2Rel.rms_norm {shard} {hidden} hin (by decide) (by decide) rfl"]
    lines += ["    exact RelationState.Holds.mono_insert hframe hout (by native_decide)", ""]
    return "\n".join(lines)


def compose_full_topology(ir: GoalIR, module_prefix: str) -> CompositionResult:
    match = _match_hidden_embedding_alltoall_two(ir)
    if isinstance(match, CompositionResult):
        return match
    return CompositionResult(
        "embedding-hidden-alltoall-two",
        _render_hidden_embedding_alltoall_two(ir, match, module_prefix),
        (),
    )
