"""Generic full-topology certificate composers.

The first registered composition rule covers a two-rank hidden-sharded
embedding followed by AllToAll(idim=1, odim=0).  Every tensor id and dimension
is derived from GoalIR; no model or layer identifiers are embedded here.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum

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
    node_index: int | None = None


@dataclass(frozen=True)
class CompositionResult:
    rule_id: str | None
    lean_source: str
    diagnostics: tuple[CompositionDiagnostic, ...]

    @property
    def supported(self) -> bool:
        return not self.diagnostics


def _failure(
    code: CompositionCode, message: str, node_index: int | None = None
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

def _render_mixed_final_value(
    *, name: str, graph: str, initial_store: str, final_store: str,
    final_equality: str, nodes_name: str, nodes: list[Node], position: int, output_tid: int,
    input_tids: tuple[int, ...], written_tids: set[int],
    expression: str, apply_lines: list[str],
) -> list[str]:
    """Extract one target value from a shared fold with hybrid input stores.

    Inputs written by the atomic slice are rewritten from the target prefix to
    the complete final store. Inputs never written by the slice are rewritten
    directly to the initial store. This avoids the expensive and redundant
    prefix→final→initial round trip.
    """
    target = nodes[position]
    if output_tid not in target.outs:
        raise ValueError(f"mixed target {name} does not write {output_tid}")
    before = nodes[:position]
    after = nodes[position + 1:]
    prefix = (
        f"([{', '.join(_node_text(node) for node in before)}] : List NodeDecl).foldl "
        f"(applyNodeDistributedFaithful {graph}) {initial_store}"
    )
    expression_prefix = expression.format(store=prefix)
    expression_hybrid = expression.format(store=final_store)
    expression_at_t = expression.format(store="t")
    semantic_inputs = tuple(dict.fromkeys(input_tids))
    lines = [
        f"    have {name}_prefix : {final_store} {output_tid} = {expression_prefix} := by",
        f"      simpa [{final_equality}, {nodes_name}] using",
        f"        (foldl_faithful_middle_writer {graph} {initial_store}",
        f"          [{', '.join(_node_text(node) for node in before)}]",
        f"          [{', '.join(_node_text(node) for node in after)}]",
        f"          {_node_text(target)} {output_tid}",
        f"          (fun t => {expression_at_t}) (by",
        "            intro t",
    ]
    lines.extend(f"            {line}" for line in apply_lines)
    lines.append("          ) (by native_decide) (by native_decide))")
    read_names = []
    suffix = [target, *after]
    for ordinal, tid in enumerate(semantic_inputs):
        read_name = f"{name}_read_{ordinal}"
        read_names.append(read_name)
        lines.extend([
            f"    have {read_name} : {prefix} {tid} = {final_store} {tid} := by",
            f"      simpa [{final_equality}, {nodes_name}] using",
            f"        (foldl_faithful_prefix_read_eq_final {graph} {initial_store}",
            f"          [{', '.join(_node_text(node) for node in before)}]",
            f"          [{', '.join(_node_text(node) for node in suffix)}] {tid}",
            "          (by native_decide) (by native_decide))",
        ])
    lines.append(f"    have {name} : {final_store} {output_tid} = {expression_hybrid} := by")
    if read_names:
        lines.extend([
            "      calc",
            f"        _ = {expression_prefix} := {name}_prefix",
            f"        _ = {expression_hybrid} := by rw [{', '.join(read_names)}]",
        ])
    else:
        lines.append(f"      exact {name}_prefix")
    return lines

def render_closed_mixed_moe_segment(ir: GoalIR, relation, segment_id: str) -> str:
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("mixed MoE renderer requires a complete closed chain")
    segment = next((x for x in chain.segments if x.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 16:
        raise ValueError("mixed MoE renderer requires one 16-transition atomic component")
    by_id = {x.transition_id: x for x in relation.transition_specs}
    transitions = [by_id[x] for x in segment.transition_ids]
    ordinary_rules = (
        "FW_norm_linear-full-producer-chunks-ordinary-two-rank",
        "identity-reshape-ordinary-two-rank", "identity-reshape-ordinary-two-rank",
        "identity-reshape-ordinary-two-rank", "mix-precision-linear-ordinary-two-rank",
        "mix-precision-linear-ordinary-two-rank", "mix-precision-linear-ordinary-two-rank",
        "topk-routing-two-output-ordinary-two-rank",
        "identity-view-ordinary-two-rank", "identity-view-ordinary-two-rank",
        "identity-view-ordinary-two-rank", "ordinary-full-moe-expert-split-two-rank",
        "sigmoid-ordinary-two-rank", "swiglu-ordinary-two-rank",
        "identity-reshape-ordinary-two-rank", "mix-precision-linear-ordinary-two-rank",
    )
    zigzag_rules = tuple(
        "zigzag-full-moe-expert-split-two-rank" if rule == "ordinary-full-moe-expert-split-two-rank"
        else rule.replace("-ordinary-two-rank", "-zigzag-two-rank")
        for rule in ordinary_rules
    )
    rules = tuple(x.rule_id for x in transitions)
    if rules == ordinary_rules:
        layout = "ordinary"
        relation_ns = "Ordinary2Rel"
    elif rules == zigzag_rules:
        layout = "zigzag"
        relation_ns = "GeneratedPatterns.Zigzag2Rel"
    else:
        raise ValueError("mixed MoE renderer received a malformed ordinary/zigzag component")
    records = {x.source: x for x in chain.relation_facts}
    states = {x.state_id: x for x in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    sms = ir.sm_nodes[slice(*segment.sm_range)]
    pms = ir.pm_nodes[slice(*segment.pm_range)]
    if len(sms) != 17 or len(pms) != 37:
        raise ValueError("mixed MoE footprint is not 17x37")
    sm_start, pm_start = segment.sm_range[0], segment.pm_range[0]
    sm_text, pm_text = [_node_text(x) for x in sms], [_node_text(x) for x in pms]
    authority = {x.fact_id: x for x in chain.authority_facts}
    live_authority = [authority[x] for x in before.fact_ids if x in authority]

    def authority_one(kind: str, predicate, label: str):
        found = [x for x in live_authority if x.kind == kind and predicate(x)]
        if len(found) != 1:
            raise ValueError(f"mixed MoE lacks unique live {label}: {len(found)}")
        return found[0]

    def common(exact: str):
        return [
            "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "  (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "simp [applyNodeDistributed, applyNodeRingAttn]", exact,
        ]

    def value_spec(graph: str, node: Node, out: int):
        ins, params = node.ins, node.params or []
        if node.op == "FW_float":
            return f"{{store}} {ins[0]}", common(
                f"exact applyNode_fw_float_out {graph} t {node.rank} {ins[0]} {out} []")
        if node.op == "FW_reshape":
            expr = f"{{store}} {ins[0]}" if not params else f"fw_view {_shape_text(params)} ({{store}} {ins[0]})"
            return expr, common(
                f"exact applyNode_fw_reshape_out {graph} t {node.rank} {ins[0]} {out} {_shape_text(params)}")
        if node.op == "FW_view":
            return f"fw_view {_shape_text(params)} ({{store}} {ins[0]})", common(
                f"exact applyNode_fw_view_out {graph} t {node.rank} {params[0]} {_shape_text(params[1:])} {ins[0]} {out}")
        if node.op == "FW_norm_linear":
            return f"fw_norm_linear ({{store}} {ins[0]}) ({{store}} {ins[1]})", common(
                f"exact applyNode_fw_norm_linear_out {graph} t {node.rank} {ins[0]} {ins[1]} {out} []")
        if node.op == "FW_mix_precision_linear":
            return f"fw_linear ({{store}} {ins[0]}) ({{store}} {ins[1]})", common(
                f"exact applyNode_fw_mix_precision_linear_out_1p {graph} t {node.rank} {ins[0]} {ins[1]} {out}")
        if node.op == "FW_sigmoid":
            return f"fw_sigmoid ({{store}} {ins[0]})", common(
                f"exact applyNode_fw_sigmoid_out_1p {graph} t {node.rank} {ins[0]} {out}")
        if node.op == "FW_swiglu":
            return f"fw_swiglu ({{store}} {ins[0]}) ({{store}} {ins[1]})", common(
                f"exact applyNode_fw_swiglu_out_1p {graph} t {node.rank} {ins[0]} {ins[1]} {out}")
        if node.op == "AllGatherPrim":
            return f"allGatherPrimDimN 0 2 0 [{{store}} {ins[0]}, {{store}} {ins[1]}]", common(
                f"rw [applyNode_allGatherPrimDimN_out {graph} t 0 [{ins[0]}, {ins[1]}] {out} 0, show {graph}.numRanks = 2 by rfl]") + ["simp"]
        if node.op == "ChunkPrim":
            return f"chunkPrimDimN 0 2 {node.rank} ({{store}} {ins[0]})", common(
                f"rw [applyNode_chunkPrimDimN_out {graph} t {node.rank} {ins[0]} {out} 0, show {graph}.numRanks = 2 by rfl]")
        if node.op == "FW_topk_routing":
            idx = node.outs.index(out)
            selector = (".fst", ".snd.fst", ".snd.snd")[idx]
            expr = (f"(fw_topk_routing ({{store}} {ins[0]}) ({_shape_text(params)}.getD 0 1) "
                    f"((({{store}} {ins[0]}).shape.reverse.head?).getD ({_shape_text(params)}.getD 1 1))){selector}")
            lemma = ("probs", "map", "scores")[idx]
            extra = "" if idx == 0 else (" (by decide)" if idx == 1 else " (by decide) (by decide)")
            return expr, common(
                f"simpa using (applyNode_fw_topk_routing_{lemma}_out {graph} t {node.rank} {ins[0]} "
                f"{node.outs[0]} {node.outs[1]} {node.outs[2]} {_shape_text(params)}{extra})")
        if node.op == "FW_all2all_moe_gmm":
            if out != node.outs[0] or len(ins) != 5 or len(params) != 4:
                raise ValueError("malformed mixed full-expert MoE writer")
            if graph == ir.sm_graph_ref:
                buddies = [node]
                weights13 = f"[{{store}} {ins[3]}]"
                weights2 = f"[{{store}} {ins[4]}]"
            elif graph == ir.pm_graph_ref:
                absolute = pm_start + pms.index(node)
                owners = [transition for transition in transitions if absolute in transition.pm_node_indices]
                if len(owners) != 1:
                    raise ValueError("mixed PM MoE writer lacks a unique atomic owner")
                peers = [ir.pm_nodes[index] for index in owners[0].pm_node_indices
                         if ir.pm_nodes[index].op == node.op]
                peers.sort(key=lambda candidate: candidate.rank)
                if len(peers) != 2 or [candidate.rank for candidate in peers] != [0, 1]:
                    raise ValueError("mixed PM MoE writer lacks exact rank-ordered pair")
                buddies = peers
                weights13 = f"[{{store}} {peers[0].ins[3]}, {{store}} {peers[1].ins[3]}]"
                weights2 = f"[{{store}} {peers[0].ins[4]}, {{store}} {peers[1].ins[4]}]"
            else:
                raise ValueError("mixed MoE writer uses unknown graph")
            expr = (f"fw_all2all_moe_gmm_full ({{store}} {ins[0]}) ({{store}} {ins[1]}) "
                    f"({{store}} {ins[2]}) {weights13} {weights2} {params[0]} {params[3]} "
                    "(((10 : Nat) : Scalar))")
            apply = [
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
                "  (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
                f"rw [applyNodeDistributed_moe_out {graph} t {node.rank} {' '.join(str(x) for x in ins)} {out} {_shape_text(params)}]",
                "unfold applyNodeFullExpertMoE_value",
                f"rw [show {graph}.replicaBuddies {_node_text(node)} = [{', '.join(_node_text(peer) for peer in buddies)}] by native_decide]",
                "rfl",
            ]
            return expr, apply
        raise ValueError(f"unsupported mixed writer operator: {node.op}")

    sm_nodes_name = f"{segment.segment_id}_sm_nodes"
    pm_nodes_name = f"{segment.segment_id}_pm_nodes"
    node_defs = [
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(sm_text)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(pm_text)}]",
        "",
    ]
    sound_name = f"{segment.segment_id}_sound"
    lines = [
        f"-- layout: {layout}",
        f"private theorem {sound_name} : ∀ smStore pmStore smResult pmResult,",
        f"    smResult = {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore →",
        f"    pmResult = {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore →",
        f"    (∀ fact ∈ {before.state_id}.facts, fact.Holds smStore pmStore) →",
        f"    ∀ fact ∈ {after.state_id}.facts, fact.Holds smResult pmResult := by",
        "    intro smStore pmStore smResult pmResult hsmResult hpmResult hstate",
        "    subst smResult",
        "    subst pmResult",
        f"    let smNodes : List NodeDecl := {sm_nodes_name}",
        f"    let pmNodes : List NodeDecl := {pm_nodes_name}",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide",
        "      · simp only [smNodes]", "        native_decide",
        "      · simp only [pmNodes]", "        native_decide",
    ]
    value_names = {}
    writer_entries = []
    writer_results = []
    def ensure_value(side: str, absolute_index: int, out: int) -> str:
        key = (side, absolute_index, out)
        if key in value_names:
            return value_names[key]
        if side == "sm":
            nodes, graph, store, final, node_name, base = sms, ir.sm_graph_ref, "smStore", "smFinal", sm_nodes_name, sm_start
        elif side == "pm":
            nodes, graph, store, final, node_name, base = pms, ir.pm_graph_ref, "pmStore", "pmFinal", pm_nodes_name, pm_start
        else:
            raise ValueError(f"unknown mixed side: {side}")
        pos = absolute_index - base
        if pos < 0 or pos >= len(nodes):
            raise ValueError(f"mixed writer index outside slice: {side}:{absolute_index}")
        node = nodes[pos]
        if out not in node.outs or any(out in later.outs for later in nodes[pos + 1:]):
            raise ValueError(f"mixed writer is not final for TID: {side}:{absolute_index}:{out}")
        ordinal = node.outs.index(out)
        expression, apply_lines = value_spec(graph, node, out)
        semantic_inputs = list(node.ins)
        if node.op == "FW_all2all_moe_gmm" and side == "pm":
            owners = [transition for transition in transitions if absolute_index in transition.pm_node_indices]
            if len(owners) != 1:
                raise ValueError("mixed PM MoE writer lacks one semantic-read owner")
            peers = [ir.pm_nodes[index] for index in owners[0].pm_node_indices
                     if ir.pm_nodes[index].op == node.op]
            peers.sort(key=lambda candidate: candidate.rank)
            if len(peers) != 2 or [candidate.rank for candidate in peers] != [0, 1]:
                raise ValueError("mixed PM MoE writer lacks rank-ordered semantic reads")
            semantic_inputs.extend([peers[0].ins[3], peers[1].ins[3], peers[0].ins[4], peers[1].ins[4]])
        semantic_inputs = tuple(dict.fromkeys(semantic_inputs))
        written = sm_written if side == "sm" else pm_written
        hybrid_expression = expression.format(store=final)
        name = f"hval_{side}_{absolute_index}_{ordinal}"
        value_names[key] = name
        result = f"{final} {out} = {hybrid_expression}"
        proof_lines = _render_mixed_final_value(
            name=name, graph=graph, initial_store=store, final_store=final,
            final_equality=("hsm" if side == "sm" else "hpm"),
            nodes_name=node_name, nodes=nodes, position=pos, output_tid=out,
            input_tids=semantic_inputs, written_tids=written,
            expression=expression, apply_lines=apply_lines)
        membership = [i for i, transition in enumerate(transitions)
                      if absolute_index in (transition.sm_node_indices if side == "sm" else transition.pm_node_indices)]
        if len(membership) != 1:
            raise ValueError(f"mixed writer has non-unique transition owner: {side}:{absolute_index}:{membership}")
        writer_results.append((name, result))
        writer_entries.append((membership[0], side, node.op, name, result, proof_lines))
        return name

    def rel_text(rec, sm_store="smFinal", pm_store="pmFinal"):
        if rec.kind == "ordinary":
            return (f"GeneratedPatterns.Ordinary2Rel ({sm_store} {rec.sm_tid}) "
                    f"({pm_store} {rec.pm_rank0_tid}) ({pm_store} {rec.pm_rank1_tid}) "
                    f"{_shape_text(list(rec.full_shape))} {_shape_text(list(rec.shard_shape))}")
        if rec.kind == "zigzag":
            return (f"GeneratedPatterns.Zigzag2Rel ({sm_store} {rec.sm_tid}) "
                    f"({pm_store} {rec.pm_rank0_tid}) ({pm_store} {rec.pm_rank1_tid}) "
                    f"({pm_store} {rec.metadata_tid}) {_shape_text(list(rec.full_shape))} "
                    f"{_shape_text(list(rec.shard_shape))}")
        raise ValueError(f"mixed semantic result is not an ordinary/zigzag fact: {rec.fact_id}")

    proved = {}
    initial_fact_ids = set(before.fact_ids)
    sm_written = {tid for node in sms for tid in node.outs}
    pm_written = {tid for node in pms for tid in node.outs}
    preserved = {}

    def preserve_initial(side: str, tid: int) -> str:
        key = (side, tid)
        if key in preserved:
            return preserved[key]
        if side == "sm":
            graph, store, final, nodes_name, written = ir.sm_graph_ref, "smStore", "smFinal", "smNodes", sm_written
        elif side == "pm":
            graph, store, final, nodes_name, written = ir.pm_graph_ref, "pmStore", "pmFinal", "pmNodes", pm_written
        else:
            raise ValueError(f"unknown mixed preservation side: {side}")
        if tid in written:
            raise ValueError(f"mixed input {side}:{tid} is written inside the atomic component")
        name = f"hpres_{side}_{tid}"
        preserved[key] = name
        lines.extend([
            f"    have {name} : {final} {tid} = {store} {tid} := by",
            "      symm",
            f"      simpa [{final}] using",
            f"        (foldl_faithful_prefix_read_eq_final {graph} {store}",
            f"          [] {nodes_name} {tid} (by native_decide) (by native_decide))",
        ])
        return name

    def writer_with_initial_inputs(name: str, side: str, node: Node) -> str:
        # _render_mixed_final_value already selects initial/final per semantic read.
        return name

    decoded_cu = None
    if layout == "zigzag":
        zigzag_records = [records[source] for transition in transitions
                           for source in (*transition.pre_facts, *transition.post_facts)
                           if records[source].kind == "zigzag"]
        metadata_tids = {record.metadata_tid for record in zigzag_records}
        metadata_regions = {record.metadata_region_id for record in zigzag_records}
        if len(metadata_tids) != 1:
            raise ValueError(f"mixed zigzag component lacks one metadata TID: {sorted(metadata_tids)}")
        if len(metadata_regions) != 1 or None in metadata_regions:
            raise ValueError(f"mixed zigzag component lacks one exact metadata region: {sorted(metadata_regions, key=str)}")
        metadata_tid = metadata_tids.pop()
        metadata_eq = authority_one(
            "tensor_eq",
            lambda fact: fact.left_side == "pm" and fact.left_tid == metadata_tid
            and fact.right_side == "pm",
            f"zigzag metadata equality {metadata_tid}")
        packed_cu = authority_one(
            "packed_cu",
            lambda fact: fact.side == "pm" and fact.tid == metadata_eq.right_tid
            and fact.total_tokens == zigzag_records[0].full_shape[0]
            and fact.num_ranks == 2,
            f"packed cu-seqlens for metadata {metadata_tid}")
        lines.extend([
            f"    have hMetadataEq : pmFinal {metadata_tid} = pmFinal {metadata_eq.right_tid} := by",
            f"      simpa [{metadata_eq.fact_id}, RelationFact.Holds, StoreSide.read] using (hframe _ (by native_decide : {metadata_eq.fact_id} ∈ {before.state_id}.facts))",
            f"    have hPackedCu : ZigzagCollective.PackedCuSeqlensWF (pmFinal {metadata_eq.right_tid}) {packed_cu.total_tokens} 2 := by",
            f"      simpa [{packed_cu.fact_id}, RelationFact.Holds, StoreSide.read] using (hframe _ (by native_decide : {packed_cu.fact_id} ∈ {before.state_id}.facts))",
            f"    have hDecodedCu : decodeCuSeqlens (pmFinal {metadata_tid}) = [0, {packed_cu.total_tokens}] := by",
            "      rw [hMetadataEq]",
            "      exact hPackedCu.decoded_single",
        ])
        decoded_cu = "hDecodedCu"

    def get_fact(rec, name):
        if rec.fact_id in proved:
            return proved[rec.fact_id]
        if rec.fact_id not in initial_fact_ids:
            raise ValueError(f"mixed prerequisite has no prior proof: {rec.fact_id}")
        lines.append(f"    have {name} : {rec.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)")
        proved[rec.fact_id] = name
        return name

    # Norm-linear full producer/chunks.
    t = transitions[0]; pre, post = records[t.pre_facts[0]], records[t.post_facts[0]]
    hin = get_fact(pre, "hNormIn")
    sm_float, sm_norm = (ir.sm_nodes[i] for i in t.sm_node_indices)
    gather, pm_float0, producer0, chunk0, chunk1 = (ir.pm_nodes[i] for i in t.pm_node_indices)
    pm_float = next(n for n in pms if n.op == "FW_float" and n.rank == 1 and n.outs == pm_float0.outs)
    producer = next(n for n in pms if n.op == "FW_norm_linear" and n.rank == 1 and n.outs == producer0.outs)
    weight = sm_norm.ins[1]
    weq = authority_one("tensor_eq", lambda x: (x.left_side, x.left_tid, x.right_side, x.right_tid) == ("sm", weight, "pm", weight), f"norm weight equality {weight}")
    wshape = authority_one("tensor_shape", lambda x: (x.side, x.tid, x.shape) == ("pm", weight, (post.shard_shape[1], pre.shard_shape[1])), f"norm weight shape {weight}")
    lines += [
        f"    have hNormWEq : smFinal {weight} = pmFinal {weight} := by",
        f"      simpa [{weq.fact_id}, RelationFact.Holds, StoreSide.read] using (hframe _ (by native_decide : {weq.fact_id} ∈ {before.state_id}.facts))",
        f"    have hNormWShape : (pmFinal {weight}).shape = {_shape_text(list(wshape.shape))} := by",
        f"      simpa [{wshape.fact_id}, RelationFact.Holds, StoreSide.read] using (hframe _ (by native_decide : {wshape.fact_id} ∈ {before.state_id}.facts))",
        f"    have hSmNorm := {writer_with_initial_inputs(ensure_value('sm', t.sm_node_indices[-1], sm_norm.outs[0]), 'sm', sm_norm)}",
        f"    rw [{writer_with_initial_inputs(ensure_value('sm', t.sm_node_indices[0], sm_float.outs[0]), 'sm', sm_float)}] at hSmNorm",
        f"    have hPmProducer := {writer_with_initial_inputs(ensure_value('pm', pm_start + pms.index(producer), producer.outs[0]), 'pm', producer)}",
        f"    rw [{writer_with_initial_inputs(ensure_value('pm', pm_start + pms.index(pm_float), pm_float.outs[0]), 'pm', pm_float)}] at hPmProducer",
        f"    have hFact0 : {post.fact_id}.Holds smFinal pmFinal := by",
        f"      change {rel_text(post)}",
        f"      exact {relation_ns}.norm_linear_fullProducer_chunks {pre.shard_shape[0]} {pre.shard_shape[1]} {post.shard_shape[1]}",
        f"        {hin} hNormWShape hNormWEq hSmNorm {writer_with_initial_inputs(ensure_value('pm', t.pm_node_indices[0], gather.outs[0]), 'pm', gather)} hPmProducer",
        f"        {writer_with_initial_inputs(ensure_value('pm', t.pm_node_indices[-2], chunk0.outs[0]), 'pm', chunk0)} {writer_with_initial_inputs(ensure_value('pm', t.pm_node_indices[-1], chunk1.outs[0]), 'pm', chunk1)} "
        + (("(by decide) (by decide) (by decide) (by decide) " + decoded_cu) if layout == "zigzag"
           else "(by decide) (by decide) (by decide)"),
    ]
    proved[post.fact_id] = "hFact0"

    # Remaining ordinary non-MoE transitions up to routing, then views.
    for number in list(range(1, 11)) + list(range(12, 16)):
        t = transitions[number]
        pres, posts = [records[x] for x in t.pre_facts], [records[x] for x in t.post_facts]
        if number == 7:
            hin = get_fact(pres[0], "hRouteIn")
            sm, p0, p1 = ir.sm_nodes[t.sm_node_indices[0]], ir.pm_nodes[t.pm_node_indices[0]], ir.pm_nodes[t.pm_node_indices[1]]
            names = []
            for label, node, side, idx in (("Sm", sm, "sm", t.sm_node_indices[0]), ("P0", p0, "pm", t.pm_node_indices[0]), ("P1", p1, "pm", t.pm_node_indices[1])):
                for oi in (0, 1):
                    src = writer_with_initial_inputs(ensure_value(side, idx, node.outs[oi]), side, node)
                    nm = f"hRoute{label}{oi}"
                    shape_field = "full_shape" if side == "sm" else ("rank0_shape" if label == "P0" else "rank1_shape")
                    lines += [f"    have {nm} := {src}", f"    rw [{hin}.{shape_field}] at {nm}", f"    simp at {nm}"]
                    names.append(nm)
            route_rewrites_a = f"{names[0]}, {names[2]}, {names[4]}"
            route_rewrites_b = f"{names[1]}, {names[3]}, {names[5]}"
            route_args = ("(by decide) (by decide) (by decide) " + decoded_cu
                          if layout == "zigzag" else "(by decide) (by decide)")
            route_second = "hRouteCore.2.1" if layout == "zigzag" else "hRouteCore.2"
            lines += [
                (
                    f"    have hRouteCore := {relation_ns}.topk_routing_all "
                    f"{pres[0].shard_shape[0]} {pres[0].shard_shape[1]} {sm.params[0]} {hin} {route_args}"
                ),
                f"    have hFact{number}a : {posts[0].fact_id}.Holds smFinal pmFinal := by",
                f"      change {rel_text(posts[0])}", f"      rw [{route_rewrites_a}]", "      exact hRouteCore.1",
                f"    have hFact{number}b : {posts[1].fact_id}.Holds smFinal pmFinal := by",
                f"      change {rel_text(posts[1])}", f"      rw [{route_rewrites_b}]", f"      exact {route_second}",
            ]
            proved[posts[0].fact_id], proved[posts[1].fact_id] = f"hFact{number}a", f"hFact{number}b"
            continue
        in_names = [get_fact(x, f"hPre{number}_{i}") for i, x in enumerate(pres)]
        sm, p0, p1 = ir.sm_nodes[t.sm_node_indices[0]], ir.pm_nodes[t.pm_node_indices[0]], ir.pm_nodes[t.pm_node_indices[1]]
        hsm = writer_with_initial_inputs(ensure_value("sm", t.sm_node_indices[0], sm.outs[0]), "sm", sm)
        hp0 = writer_with_initial_inputs(ensure_value("pm", t.pm_node_indices[0], p0.outs[0]), "pm", p0)
        hp1 = writer_with_initial_inputs(ensure_value("pm", t.pm_node_indices[1], p1.outs[0]), "pm", p1)
        post = posts[0]
        relation_rewrites = f"{hsm}, {hp0}, {hp1}"
        lines += [f"    have hFact{number} : {post.fact_id}.Holds smFinal pmFinal := by", f"      change {rel_text(post)}", f"      rw [{relation_rewrites}]"]
        if t.rule_id.startswith("identity-"):
            if layout == "zigzag":
                lines += [f"      exact GeneratedPatterns.Zigzag2Rel.view_id {post.shard_shape[0]} {post.shard_shape[1]} {in_names[0]}"]
            else:
                lines += [f"      exact Ordinary2Rel.view_id {in_names[0]}"]
        elif t.rule_id == f"mix-precision-linear-{layout}-two-rank":
            weight = sm.ins[1]; in_dim = pres[0].shard_shape[1]; out_dim = post.shard_shape[1]; rows = pres[0].shard_shape[0]
            weq = authority_one("tensor_eq", lambda x, w=weight: (x.left_side, x.left_tid, x.right_side, x.right_tid) == ("sm", w, "pm", w), f"linear equality {weight}")
            wshape = authority_one("tensor_shape", lambda x, w=weight, sh=(out_dim, in_dim): (x.side, x.tid, x.shape) == ("pm", w, sh), f"linear shape {weight}")
            lines[-1:-1] = [
                f"      have hwEq : smFinal {weight} = pmFinal {weight} := by",
                f"        simpa [{weq.fact_id}, RelationFact.Holds, StoreSide.read] using (hframe _ (by native_decide : {weq.fact_id} ∈ {before.state_id}.facts))",
                f"      have hwShape : (pmFinal {weight}).shape = {_shape_text([out_dim, in_dim])} := by",
                f"        simpa [{wshape.fact_id}, RelationFact.Holds, StoreSide.read] using (hframe _ (by native_decide : {wshape.fact_id} ∈ {before.state_id}.facts))",
            ]
            if layout == "zigzag":
                lines += ["      rw [hwEq]", f"      exact GeneratedPatterns.Zigzag2Rel.mix_precision_linear {rows} {in_dim} {out_dim} {in_names[0]} hwShape (by decide) (by decide) (by decide)"]
            else:
                lines += [f"      exact Ordinary2Rel.mix_precision_linear {rows} {in_dim} {out_dim} {in_names[0]} hwShape hwEq (by decide) (by decide) (by decide)"]
        elif t.rule_id == f"sigmoid-{layout}-two-rank":
            rows, hidden = post.shard_shape
            lines += [f"      exact {relation_ns}.sigmoid {rows} {hidden} {in_names[0]} (by decide) (by decide)"]
        elif t.rule_id == f"swiglu-{layout}-two-rank":
            rows, hidden = post.shard_shape
            lines += [f"      exact {relation_ns}.swiglu {rows} {hidden} {in_names[0]} {in_names[1]} (by decide) (by decide)"]
        else:
            raise ValueError(f"unsupported {layout} mixed relation: {t.rule_id}")
        proved[post.fact_id] = f"hFact{number}"

    # MoE transition is emitted after routing and before state publication.
    t = transitions[11]; pres, post = [records[x] for x in t.pre_facts], records[t.post_facts[0]]
    sm, p0, p1 = ir.sm_nodes[t.sm_node_indices[0]], ir.pm_nodes[t.pm_node_indices[0]], ir.pm_nodes[t.pm_node_indices[1]]
    def moe_role(index: int, label: str) -> str:
        matches = [fact for fact in pres
                   if (fact.sm_tid, fact.pm_rank0_tid, fact.pm_rank1_tid)
                   == (sm.ins[index], p0.ins[index], p1.ins[index])]
        if len(matches) != 1:
            raise ValueError(f"mixed MoE {label} role has {len(matches)} exact TID matches")
        return get_fact(matches[0], f"hMoe{label}")
    hX, hRP, hRM = moe_role(0, "Input"), moe_role(1, "Probs"), moe_role(2, "Routing")
    if any(node.params is None or len(node.params) != 4 for node in (sm, p0, p1)):
        raise ValueError("mixed MoE requires four closed parameters")
    num_exp, top_k = sm.params[0], sm.params[3]
    if any((node.params[0], node.params[3]) != (num_exp, top_k) for node in (p0, p1)):
        raise ValueError("mixed MoE numExp/topK parameters disagree")
    gathers = []
    for weight, a, b in ((sm.ins[3], p0.ins[3], p1.ins[3]), (sm.ins[4], p0.ins[4], p1.ins[4])):
        gathers.append(authority_one("gather", lambda x, W=weight, A=a, B=b: (x.sm_tid, x.pm_rank0_tid, x.pm_rank1_tid, x.dim) == (W, A, B, 0), f"MoE gather {weight}"))
    lines += [
        f"    have hW13 : {gathers[0].fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    have hW2 : {gathers[1].fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        "    have hW13Value := hW13.1",
        "    have hW13FullShape := hW13.2.1",
        "    have hW13Rank0Shape := hW13.2.2.1",
        "    have hW13Rank1Shape := hW13.2.2.2",
        "    have hW2Value := hW2.1",
        "    have hW2FullShape := hW2.2.1",
        "    have hW2Rank0Shape := hW2.2.2.1",
        "    have hW2Rank1Shape := hW2.2.2.2",
    ]
    # Exact MoE writers are emitted through the same transition-owned helper bundle.
    moe_locals = {
        "Sm": writer_with_initial_inputs(
            ensure_value("sm", t.sm_node_indices[0], sm.outs[0]), "sm", sm),
        "P0": writer_with_initial_inputs(
            ensure_value("pm", t.pm_node_indices[0], p0.outs[0]), "pm", p0),
        "P1": writer_with_initial_inputs(
            ensure_value("pm", t.pm_node_indices[1], p1.outs[0]), "pm", p1),
    }
    if layout == "ordinary":
        lines += [
        "    have hMoeSm : smFinal " + str(sm.outs[0]) + " = fw_all2all_moe_gmm_full "
        + f"(smFinal {sm.ins[0]}) (smFinal {sm.ins[1]}) (smFinal {sm.ins[2]}) [pmFinal {p0.ins[3]}, pmFinal {p1.ins[3]}] [pmFinal {p0.ins[4]}, pmFinal {p1.ins[4]}] {num_exp} {top_k} (((10 : Nat) : Scalar)) := by",
        f"      rw [{moe_locals['Sm']}]", "      unfold fw_all2all_moe_gmm_full", "      simp only [List.length_cons, List.length_nil]",
        "      rw [allGatherPrimDimN_singleton_eq 0 _ (by rw [hW13FullShape]; decide),",
        "        allGatherPrimDimN_singleton_eq 0 _ (by rw [hW2FullShape]; decide), hW13Value, hW2Value]",
        f"    have hMoeSmShape : (smFinal {sm.outs[0]}).shape = {_shape_text(list(post.full_shape))} := by",
        f"      rw [{moe_locals['Sm']}]", f"      exact fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ {post.full_shape[0]} {post.full_shape[1]} (by rw [{hX}.full_shape]; rfl) (by rw [{hX}.full_shape]; rfl)",
        f"    have hMoeP0Shape : (pmFinal {p0.outs[0]}).shape = {_shape_text(list(post.shard_shape))} := by",
        f"      rw [{moe_locals['P0']}]", f"      exact fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ {post.shard_shape[0]} {post.shard_shape[1]} (by rw [{hX}.rank0_shape]; rfl) (by rw [{hX}.rank0_shape]; rfl)",
        f"    have hMoeP1Shape : (pmFinal {p1.outs[0]}).shape = {_shape_text(list(post.shard_shape))} := by",
        f"      rw [{moe_locals['P1']}]", f"      exact fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ {post.shard_shape[0]} {post.shard_shape[1]} (by rw [{hX}.rank1_shape]; rfl) (by rw [{hX}.rank1_shape]; rfl)",
        f"    have hMoeInputGather := Ordinary2Rel.toGather2Rel {hX} (by decide)",
        f"    have hMoeProbsGather := Ordinary2Rel.toGather2Rel {hRP} (by decide)",
        f"    have hMoeRoutingGather := Ordinary2Rel.toGather2Rel {hRM} (by decide)",
        f"    have hMoeGather := GeneratedPatterns.gather2Rel_fullExpertMoE_boundary (input := smFinal {sm.ins[0]}) (input0 := pmFinal {p0.ins[0]}) (input1 := pmFinal {p1.ins[0]})",
        f"      (rp := smFinal {sm.ins[1]}) (rp0 := pmFinal {p0.ins[1]}) (rp1 := pmFinal {p1.ins[1]})",
        f"      (rm := smFinal {sm.ins[2]}) (rm0 := pmFinal {p0.ins[2]}) (rm1 := pmFinal {p1.ins[2]})",
        f"      (w130 := pmFinal {p0.ins[3]}) (w131 := pmFinal {p1.ins[3]}) (w20 := pmFinal {p0.ins[4]}) (w21 := pmFinal {p1.ins[4]})",
        f"      (out := smFinal {sm.outs[0]}) (out0 := pmFinal {p0.outs[0]}) (out1 := pmFinal {p1.outs[0]})",
        f"      (L := {post.shard_shape[0]}) (hM := {post.shard_shape[1]}) (E := {gathers[0].shard_shape[0]}) (topK := {sm.params[3]})",
        f"      (tDim := {gathers[0].shard_shape[1]}) (dDim := {gathers[1].shard_shape[2]}) (swigluLimit := (((10 : Nat) : Scalar)))",
        "      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hMoeInputGather hMoeProbsGather hMoeRoutingGather",
        f"      hW13Rank0Shape hW13Rank1Shape hW2Rank0Shape hW2Rank1Shape hMoeSm {moe_locals['P0']} {moe_locals['P1']} hMoeSmShape hMoeP0Shape hMoeP1Shape",
        f"    have hFact11 : {post.fact_id}.Holds smFinal pmFinal := ⟨hMoeGather.value, hMoeGather.full_shape, hMoeGather.shard0_shape, hMoeGather.shard1_shape⟩",
    ]
    else:
        lines += [
            f"    have hFact11 : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change {rel_text(post)}",
            f"      rw [{moe_locals['Sm']}, {moe_locals['P0']}, {moe_locals['P1']}]",
            "      exact GeneratedPatterns.Zigzag2Rel.all2all_moe_gmm_full_1x2",
            f"        (w13 := smFinal {sm.ins[3]}) (w2 := smFinal {sm.ins[4]})",
            f"        (w13a := pmFinal {p0.ins[3]}) (w13b := pmFinal {p1.ins[3]})",
            f"        (w2a := pmFinal {p0.ins[4]}) (w2b := pmFinal {p1.ins[4]})",
            f"        (lDim := {post.shard_shape[0]}) (hModel := {post.shard_shape[1]})",
            f"        (numExp := {sm.params[0]}) (topK := {sm.params[3]})",
            f"        (tDim := {gathers[0].full_shape[1]}) (dDim := {gathers[1].full_shape[2]})",
            "        (swigluLimit := (((10 : Nat) : Scalar)))",
            f"        {hX} {hRP} {hRM} (by decide) (by decide) (by decide) (by decide) rfl",
            f"        hW13FullShape hW2FullShape hW13Value hW2Value {decoded_cu}",
        ]
    proved[post.fact_id] = "hFact11"

    fact_by_id = {x.fact_id: x for x in chain.relation_facts}
    fresh = [fact_by_id[x] for x in after.fact_ids if x not in before.fact_ids]
    expected_fresh = [records[transitions[i].post_facts[0]] for i in (11, 12, 15)]
    if [x.fact_id for x in fresh] != [x.fact_id for x in expected_fresh]:
        raise ValueError("mixed MoE post-state fresh fact set/order mismatch")
    lines += [
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(x.fact_id for x in fresh)}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(x.fact_id for x in fresh)}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with rfl | rfl | rfl",
        f"      · exact {proved[fresh[0].fact_id]}", f"      · exact {proved[fresh[1].fact_id]}", f"      · exact {proved[fresh[2].fact_id]}",
        "    · exact hframe fact old", "",
        f"private def {segment.segment_id}_eq :",
        f"    ClosedDepSegmentCertificateEq {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}",
        f"  pmNodes := {pm_nodes_name}",
        "  sound := by",
        "    intro smStore pmStore smResult pmResult hsm hpm hpre",
        f"    exact {sound_name} smStore pmStore smResult pmResult hsm hpm hpre",
        "",
        f"private noncomputable def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} :=",
        f"  {segment.segment_id}_eq.toCertificate",
        "",
    ]
    if not writer_entries:
        raise ValueError("mixed MoE segment produced no writer obligations")
    helper = []
    unpack = []
    def writer_group_key(entry):
        return entry[1]

    for group_side in sorted({writer_group_key(entry) for entry in writer_entries}):
        entries = [entry for entry in writer_entries if writer_group_key(entry) == group_side]
        writer_theorem = f"{segment.segment_id}_{group_side}_writer_values"
        if group_side == "sm":
            helper.extend([
                f"private theorem {writer_theorem} (smStore smFinal : Store)",
                f"    (hsm : smFinal = {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore) :",
                "    " + " ∧\n    ".join(result for _, _, _, _, result, _ in entries) + " := by",
            ])
        else:
            helper.extend([
                f"private theorem {writer_theorem} (pmStore pmFinal : Store)",
                f"    (hpm : pmFinal = {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) :",
                "    " + " ∧\n    ".join(result for _, _, _, _, result, _ in entries) + " := by",
            ])
        for _, _, _, _, _, proof_lines in entries:
            helper.extend(line.removeprefix("  ") for line in proof_lines)
        names = [name for _, _, _, name, _, _ in entries]
        helper.extend([
            (f"  exact {names[0]}" if len(names) == 1 else "  exact ⟨" + ", ".join(names) + "⟩"),
            "",
        ])
        bundle = f"hWriterValues_{group_side}"
        if group_side == "sm":
            unpack.append(f"    have {bundle} := {writer_theorem} smStore smFinal (by rfl)")
        else:
            unpack.append(f"    have {bundle} := {writer_theorem} pmStore pmFinal (by rfl)")
        for index, name in enumerate(names):
            if len(names) == 1:
                unpack.append(f"    have {name} := {bundle}")
            else:
                projection = ".2" * index + (".1" if index < len(names) - 1 else "")
                unpack.append(f"    have {name} := {bundle}{projection}")
    unpack_index = next(i for i, line in enumerate(lines) if line.startswith("    have hNormIn :"))
    lines[unpack_index:unpack_index] = unpack

    # Reset Lean's per-declaration heartbeat budget at the semantic midpoint
    # without repeating either authority fold.  The prefix theorem consumes
    # the one-fold frame and opaque writer equalities produced by main sound.
    semantic_start = next(i for i, line in enumerate(lines) if line.startswith("    have hNormIn :"))
    semantic_split = next(i for i, line in enumerate(lines) if line.startswith("    have hFact8 "))
    prefix_outputs = [
        (records[fact_spec], proved[records[fact_spec].fact_id])
        for transition in transitions[:8]
        for fact_spec in transition.post_facts
    ]
    prefix_name = f"{segment.segment_id}_sound_prefix"
    prefix_semantic_source = "\n".join(lines[semantic_start:semantic_split])
    prefix_writer_results = [
        (name, result) for name, result in writer_results
        if name in prefix_semantic_source
    ]
    prefix_lines = [
        f"private theorem {prefix_name} (smFinal pmFinal : Store)",
        f"    (hframe : {before.state_id}.Holds smFinal pmFinal)",
    ]
    if layout == "zigzag":
        prefix_lines.append(
            f"    (hDecodedCu : decodeCuSeqlens (pmFinal {metadata_tid}) = [0, {packed_cu.total_tokens}])")
    for name, result in prefix_writer_results:
        prefix_lines.append(f"    ({name} : {result})")
    prefix_lines.extend([
        "    : " + " ∧\n    ".join(
            f"{fact.fact_id}.Holds smFinal pmFinal" for fact, _ in prefix_outputs
        ) + " := by",
        *lines[semantic_start:semantic_split],
        "    exact ⟨" + ", ".join(name for _, name in prefix_outputs) + "⟩",
        "",
    ])
    prefix_call = [
        f"    have hPrefixFacts := {prefix_name} smFinal pmFinal hframe" +
        (" hDecodedCu" if layout == "zigzag" else ""),
    ]
    for name, _ in prefix_writer_results:
        prefix_call.append(f"      {name}")
    for i, (_, name) in enumerate(prefix_outputs):
        projection = ".2" * i + (".1" if i < len(prefix_outputs) - 1 else "")
        prefix_call.append(f"    have {name} := hPrefixFacts{projection}")
    lines[semantic_start:semantic_split] = prefix_call
    return "\n".join(node_defs + helper + prefix_lines + lines)


def render_closed_rotary_segment(ir: GoalIR, relation, segment_id: str) -> str:
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("rotary renderer requires a complete closed chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("rotary renderer requires one atomic transition")
    transition = {item.transition_id: item for item in relation.transition_specs}[segment.transition_ids[0]]
    if transition.rule_id != "rotary-embedding-two-output-ordinary-two-rank":
        raise ValueError("rotary renderer received an unsupported relation family")
    if len(transition.pre_facts) != 3 or len(transition.post_facts) != 2:
        raise ValueError("rotary renderer requires three inputs and two outputs")
    facts = {item.source: item for item in chain.relation_facts}
    pre_facts = [facts[item] for item in transition.pre_facts]
    post_facts = [facts[item] for item in transition.post_facts]
    if any(item.kind != "ordinary" for item in pre_facts + post_facts):
        raise ValueError("rotary renderer requires ordinary relations")
    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    if len(sm_nodes) != 1 or len(pm_nodes) != 2:
        raise ValueError("rotary footprint is not 1xSM+2xPM")
    sm, p0, p1 = sm_nodes[0], pm_nodes[0], pm_nodes[1]
    if any(node.op != "FW_rotary_embedding" for node in (sm, p0, p1)):
        raise ValueError("rotary footprint has the wrong operator")
    if (sm.rank, p0.rank, p1.rank) != (0, 0, 1):
        raise ValueError("rotary ranks are not ordered")
    if any(len(node.ins) != 4 or len(node.outs) != 2 or len(node.params) != 2 for node in (sm, p0, p1)):
        raise ValueError("rotary node arity mismatch")
    if tuple(sm.params) != tuple(p0.params) or tuple(sm.params) != tuple(p1.params):
        raise ValueError("rotary head parameters disagree")
    if p0.ins[0] != p1.ins[0] or sm.ins[0] != p0.ins[0]:
        raise ValueError("rotary cache is not a shared replicated TID")

    def relation_for_inputs(index: int):
        matches = [item for item in pre_facts if
            (item.sm_tid, item.pm_rank0_tid, item.pm_rank1_tid) ==
            (sm.ins[index], p0.ins[index], p1.ins[index])]
        if len(matches) != 1:
            raise ValueError(f"rotary input role {index} is ambiguous")
        return matches[0]

    positions, q_rel, k_rel = (relation_for_inputs(index) for index in (1, 2, 3))
    if len(positions.shard_shape) != 1 or positions.full_shape != (2 * positions.shard_shape[0],):
        raise ValueError("rotary positions are not exact one-dimensional shards")
    l_dim = positions.shard_shape[0]
    qh, kh = sm.params
    if qh <= 0 or kh <= 0 or l_dim <= 0:
        raise ValueError("rotary dimensions must be positive")
    if q_rel.shard_shape[:2] != (l_dim, qh) or k_rel.shard_shape[:2] != (l_dim, kh):
        raise ValueError("rotary input head shapes disagree with params")
    if len(q_rel.shard_shape) != 3 or len(k_rel.shard_shape) != 3 or q_rel.shard_shape[2] != k_rel.shard_shape[2]:
        raise ValueError("rotary q/k head widths disagree")
    d_width = q_rel.shard_shape[2]
    if d_width <= 0 or q_rel.full_shape != (2 * l_dim, qh, d_width) or k_rel.full_shape != (2 * l_dim, kh, d_width):
        raise ValueError("rotary q/k full shapes are not exact ordered shards")

    def relation_for_outputs(index: int):
        matches = [item for item in post_facts if
            (item.sm_tid, item.pm_rank0_tid, item.pm_rank1_tid) ==
            (sm.outs[index], p0.outs[index], p1.outs[index])]
        if len(matches) != 1:
            raise ValueError(f"rotary output role {index} is ambiguous")
        return matches[0]

    q_out, k_out = (relation_for_outputs(index) for index in (0, 1))
    if (q_out.full_shape, q_out.shard_shape) != (q_rel.full_shape, q_rel.shard_shape):
        raise ValueError("rotary q output changes shape")
    if (k_out.full_shape, k_out.shard_shape) != (k_rel.full_shape, k_rel.shard_shape):
        raise ValueError("rotary k output changes shape")
    cache_facts = [item for item in chain.authority_facts
        if getattr(item, "kind", None) == "tensor_eq"
        and getattr(item, "left_side", None) == "sm"
        and getattr(item, "right_side", None) == "pm"
        and getattr(item, "left_tid", None) == sm.ins[0]
        and getattr(item, "right_tid", None) == p0.ins[0]]
    if len(cache_facts) != 1:
        raise ValueError("rotary replicated cache authority is missing or ambiguous")
    cache_fact = cache_facts[0]
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required_pre = {positions.fact_id, q_rel.fact_id, k_rel.fact_id, cache_fact.fact_id}
    if not required_pre <= set(before.fact_ids):
        raise ValueError("rotary prerequisites are not live")
    if not set(after.fact_ids) <= (set(before.fact_ids) | {q_out.fact_id, k_out.fact_id}):
        raise ValueError("rotary introduces an unproved state fact")
    sm_text = _node_text(sm)
    pm_text = [_node_text(p0), _node_text(p1)]

    def app(node: Node, graph: str, output_index: int, indent: str) -> list[str]:
        lemma = "applyNode_fw_rotary_embedding_fst_out" if output_index == 0 else "applyNode_fw_rotary_embedding_snd_out"
        lines = [
            indent + "intro t",
            indent + "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            indent + "  (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            indent + "simp [applyNodeDistributed, applyNodeRingAttn]",
            indent + f"exact {lemma} {graph} t {node.rank} {qh} {kh} "
                + " ".join(str(item) for item in (*node.ins, *node.outs))
                + (" (by native_decide)" if output_index == 1 else ""),
        ]
        return lines

    def output_value(name: str, graph: str, store: str, nodes: list[Node], pos: int,
                     node: Node, final: str, output_index: int) -> list[str]:
        prior, later = nodes[:pos], nodes[pos + 1:]
        projection = ".1" if output_index == 0 else ".2"
        fn = (f"(fun t => (fw_rotary_embedding (t {node.ins[0]}) (t {node.ins[1]}) "
              f"(t {node.ins[2]}) (t {node.ins[3]}) {qh} {kh}){projection})")
        lines = []
        read_names: list[str] = []
        if prior:
            prior_text = f"[{', '.join(_node_text(item) for item in prior)}]"
            for tid in node.ins:
                read_name = f"{name}_read_{tid}"
                read_names.append(read_name)
                lines += [
                    f"    have {read_name} : {prior_text}.foldl (applyNodeDistributedFaithful {graph}) {store} {tid} = {store} {tid} := by",
                    f"      exact foldl_applyNodeDistributedFaithful_at_not_written {graph} {prior_text} {store} {tid} (by native_decide) (by native_decide)",
                ]
        lines += [
            (f"    have {name} : {final} {node.outs[output_index]} = "
                f"(fw_rotary_embedding ({store} {node.ins[0]}) ({store} {node.ins[1]}) "
                f"({store} {node.ins[2]}) ({store} {node.ins[3]}) {qh} {kh}){projection} := by"),
            "      calc",
            (f"        {final} {node.outs[output_index]} = {fn} "
                f"([{', '.join(_node_text(item) for item in prior)}].foldl "
                f"(applyNodeDistributedFaithful {graph}) {store}) := by"),
            f"          simpa [{final}, {'smNodes' if final == 'smFinal' else 'pmNodes'}] using",
            f"            (foldl_faithful_middle_writer {graph} {store}",
            (f"              [{', '.join(_node_text(item) for item in prior)}] "
                f"[{', '.join(_node_text(item) for item in later)}] {_node_text(node)}"),
            f"              {node.outs[output_index]} ({fn}) (by",
        ]
        lines += app(node, graph, output_index, "                ")
        lines += ["              ) (by native_decide) (by native_decide))"]
        if prior:
            lines += [f"        _ = {fn} {store} := by", "          dsimp only", f"          rw [{', '.join(read_names)}]"]
        else:
            lines += [f"        _ = {fn} {store} := rfl"]
        return lines

    lines = [
        f"private def {segment.segment_id} (smGraph pmGraph : GraphDecl) :",
        f"    ClosedDepSegmentCertificate smGraph pmGraph {before.state_id} {after.state_id} where",
        f"  smNodes := [{sm_text}]",
        f"  pmNodes := [{', '.join(pm_text)}]",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := [{sm_text}]",
        f"    let pmNodes : List NodeDecl := [{', '.join(pm_text)}]",
        "    let smFinal := smNodes.foldl (applyNodeDistributedFaithful smGraph) smStore",
        "    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hpos : {positions.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hq : {q_rel.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hk : {k_rel.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hcache : {cache_fact.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
    ]
    for prefix, graph, store, nodes, pos, node, final in (
        ("sm", "smGraph", "smStore", sm_nodes, 0, sm, "smFinal"),
        ("p0", "pmGraph", "pmStore", pm_nodes, 0, p0, "pmFinal"),
        ("p1", "pmGraph", "pmStore", pm_nodes, 1, p1, "pmFinal"),
    ):
        lines += output_value(f"h{prefix}q", graph, store, nodes, pos, node, final, 0)
        lines += output_value(f"h{prefix}k", graph, store, nodes, pos, node, final, 1)
    q_full = _shape_text(list(q_out.full_shape)); q_shard = _shape_text(list(q_out.shard_shape))
    k_full = _shape_text(list(k_out.full_shape)); k_shard = _shape_text(list(k_out.shard_shape))
    pos_full = _shape_text(list(positions.full_shape)); pos_shard = _shape_text(list(positions.shard_shape))
    lines += [
        (f"    change GeneratedPatterns.Ordinary2Rel (smStore {positions.sm_tid}) "
            f"(pmStore {positions.pm_rank0_tid}) (pmStore {positions.pm_rank1_tid}) {pos_full} {pos_shard} at hpos"),
        (f"    change GeneratedPatterns.Ordinary2Rel (smStore {q_rel.sm_tid}) "
            f"(pmStore {q_rel.pm_rank0_tid}) (pmStore {q_rel.pm_rank1_tid}) {q_full} {q_shard} at hq"),
        (f"    change GeneratedPatterns.Ordinary2Rel (smStore {k_rel.sm_tid}) "
            f"(pmStore {k_rel.pm_rank0_tid}) (pmStore {k_rel.pm_rank1_tid}) {k_full} {k_shard} at hk"),
        f"    change smStore {sm.ins[0]} = pmStore {p0.ins[0]} at hcache",
        f"    have houts := Ordinary2Rel.rotary_embedding_1d (L := {l_dim}) (qh := {qh}) (kh := {kh}) (d := {d_width})",
        "      hpos hq hk hcache (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
        f"    have houtq : {q_out.fact_id}.Holds smFinal pmFinal := by",
        (f"      change GeneratedPatterns.Ordinary2Rel (smFinal {q_out.sm_tid}) "
            f"(pmFinal {q_out.pm_rank0_tid}) (pmFinal {q_out.pm_rank1_tid}) {q_full} {q_shard}"),
        "      rw [hsmq, hp0q, hp1q]",
        "      exact houts.1",
        f"    have houtk : {k_out.fact_id}.Holds smFinal pmFinal := by",
        (f"      change GeneratedPatterns.Ordinary2Rel (smFinal {k_out.sm_tid}) "
            f"(pmFinal {k_out.pm_rank0_tid}) (pmFinal {k_out.pm_rank1_tid}) {k_full} {k_shard}"),
        "      rw [hsmk, hp0k, hp1k]",
        "      exact houts.2",
        f"    have hqstate : ({{ facts := {q_out.fact_id} :: {before.state_id}.facts, nonempty := by decide }} : RelationState).Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.mono_insert hframe houtq",
        "      intro fact hmem",
        "      exact hmem",
        "    exact RelationState.Holds.mono_insert hqstate houtk (by native_decide)",
        "",
    ]
    return "\n".join(lines)


def _render_closed_zigzag_attention_segment(ir: GoalIR, relation,
                                                segment_id: str) -> str:
    """Render faithful zigzag attention with ordinary sharded K/V."""
    chain = relation.dependent_chain_plan
    segment = next(item for item in chain.segments if item.segment_id == segment_id)
    transitions = {item.transition_id: item for item in relation.transition_specs}
    transition = transitions[segment.transition_ids[0]]
    sm_nodes = ir.sm_nodes[segment.sm_range[0]:segment.sm_range[1]]
    pm_nodes = ir.pm_nodes[segment.pm_range[0]:segment.pm_range[1]]
    if len(sm_nodes) != 1 or len(pm_nodes) != 2:
        raise ValueError(f"{segment_id} zigzag attention requires one SM and two PM nodes")
    sm, p0, p1 = sm_nodes[0], pm_nodes[0], pm_nodes[1]
    if [sm.rank, p0.rank, p1.rank] != [0, 0, 1]:
        raise ValueError(f"{segment_id} zigzag attention rank order mismatch")
    if any(node.op != "FW_attn_zigzag" for node in (sm, p0, p1)):
        raise ValueError(f"{segment_id} zigzag attention node family mismatch")
    if any(len(node.ins) != 5 or len(node.outs) != 2 for node in (sm, p0, p1)):
        raise ValueError(f"{segment_id} malformed zigzag attention signature")
    if sm.params != p0.params or p0.params != p1.params or len(sm.params) != 6:
        raise ValueError(f"{segment_id} zigzag attention params disagree")
    if p0.ins[3:] != p1.ins[3:] or p0.ins[1] == p1.ins[1] or p0.ins[2] == p1.ins[2]:
        raise ValueError(f"{segment_id} requires exact sharded-K/V buddy inputs")

    facts = {fact.source: fact for fact in chain.relation_facts}
    pre = [facts[item] for item in transition.pre_facts]
    by_sm_tid = {fact.sm_tid: fact for fact in pre}
    if len(by_sm_tid) != len(pre):
        raise ValueError(f"{segment_id} attention facts do not bind unique SM tids")
    try:
        q_rel, k_rel, v_rel = (by_sm_tid[sm.ins[index]] for index in range(3))
    except KeyError as exc:
        raise ValueError(f"{segment_id} missing attention input role {exc.args[0]}") from exc
    if (q_rel.kind, k_rel.kind, v_rel.kind) != ("zigzag", "ordinary", "ordinary"):
        raise ValueError(f"{segment_id} requires zigzag Q and ordinary K/V")
    if len(transition.post_facts) != 1:
        raise ValueError(f"{segment_id} attention requires one output fact")
    out_rel = facts[transition.post_facts[0]]
    expected = [
        (q_rel.pm_rank0_tid, q_rel.pm_rank1_tid, p0.ins[0], p1.ins[0], "Q"),
        (k_rel.pm_rank0_tid, k_rel.pm_rank1_tid, p0.ins[1], p1.ins[1], "K"),
        (v_rel.pm_rank0_tid, v_rel.pm_rank1_tid, p0.ins[2], p1.ins[2], "V"),
        (out_rel.pm_rank0_tid, out_rel.pm_rank1_tid, p0.outs[0], p1.outs[0], "output"),
    ]
    for left0, left1, right0, right1, role in expected:
        if (left0, left1) != (right0, right1):
            raise ValueError(f"{segment_id} {role} role mismatch")
    if q_rel.sm_tid != sm.ins[0] or out_rel.sm_tid != sm.outs[0] or out_rel.kind != "zigzag":
        raise ValueError(f"{segment_id} malformed zigzag attention relation facts")
    if (q_rel.metadata_tid is None or q_rel.metadata_region_id is None or
            out_rel.metadata_tid != q_rel.metadata_tid or
            out_rel.metadata_region_id != q_rel.metadata_region_id):
        raise ValueError(f"{segment_id} zigzag metadata fact/region mismatch")

    q_full, q_shard = tuple(q_rel.full_shape), tuple(q_rel.shard_shape)
    k_full, k_shard = tuple(k_rel.full_shape), tuple(k_rel.shard_shape)
    v_full, v_shard = tuple(v_rel.full_shape), tuple(v_rel.shard_shape)
    out_full, out_shard = tuple(out_rel.full_shape), tuple(out_rel.shard_shape)
    if not (len(q_shard) == len(k_shard) == len(v_shard) == 3):
        raise ValueError(f"{segment_id} malformed attention shapes")
    l_dim, q_heads, q_dim = q_shard
    lk, kv_heads, k_dim = k_shard
    lv, v_heads, v_dim = v_shard
    if (l_dim <= 0 or lk != l_dim or lv != l_dim or k_dim != q_dim or v_heads != kv_heads or
            q_full != (2 * l_dim, q_heads, q_dim) or
            k_full != (2 * l_dim, kv_heads, q_dim) or
            v_full != (2 * l_dim, kv_heads, v_dim) or
            out_full != (2 * l_dim, q_heads, v_dim) or
            out_shard != (l_dim, q_heads, v_dim) or
            list(sm.params[:4]) != [q_heads, kv_heads, q_dim, v_dim]):
        raise ValueError(f"{segment_id} attention shape/param mismatch")

    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if not set(after.fact_ids).issubset(set(before.fact_ids) | {out_rel.fact_id}):
        raise ValueError(f"{segment_id} attention post-state contains unproved facts")
    live = set(before.fact_ids)
    authority = list(chain.authority_facts)

    def exact_eq(left_side: str, left_tid: int, right_side: str, right_tid: int,
                 diagnostic: str):
        endpoints = {(left_side, left_tid), (right_side, right_tid)}
        matches = [fact for fact in authority if fact.kind == "tensor_eq" and
                   {(fact.left_side, fact.left_tid), (fact.right_side, fact.right_tid)} == endpoints and
                   fact.fact_id in live]
        if len(matches) != 1:
            raise ValueError(f"{segment_id} expected one {diagnostic}")
        return matches[0]

    cuq_cross = exact_eq("sm", sm.ins[3], "pm", p0.ins[3], "cuQ cross-store equality")
    cukv_cross = exact_eq("sm", sm.ins[4], "pm", p0.ins[4], "cuKV cross-store equality")
    regions = [item for item in relation.zigzag_regions
               if item.region_id == q_rel.metadata_region_id]
    if len(regions) != 1:
        raise ValueError(f"{segment_id} expected one zigzag metadata region")
    region = regions[0]
    packed = [fact for fact in authority if fact.kind == "packed_cu" and
              fact.side == "pm" and fact.tid == region.contract_metadata_tid and
              fact.total_tokens == 2 * l_dim and fact.num_ranks == 2 and
              fact.fact_id in live]
    if len(packed) != 1:
        raise ValueError(f"{segment_id} expected one PackedCu authority")
    packed = packed[0]
    meta_alias = exact_eq("pm", q_rel.metadata_tid, "pm", packed.tid, "exact metadata alias")
    cuq_alias = exact_eq("pm", p0.ins[3], "pm", packed.tid, "exact metadata alias")

    params_text = _shape_text(list(sm.params))
    sm_text, p0_text, p1_text = _node_text(sm), _node_text(p0), _node_text(p1)

    def writer(name: str, graph: str, store: str, final: str,
               nodes: list[Node], pos: int) -> list[str]:
        node = nodes[pos]
        prior, tail = nodes[:pos], nodes[pos + 1:]
        prior_text = f"[{', '.join(_node_text(item) for item in prior)}]"
        tail_text = f"[{', '.join(_node_text(item) for item in tail)}]"
        node_text = _node_text(node)
        fn = f"(fun t => applyNodeFaithfulZigzagAttnValue {graph} t {node_text})"
        lines: list[str] = []
        reads: list[str] = []
        semantic_reads = tuple(dict.fromkeys(tid for buddy in nodes for tid in buddy.ins)) if prior else ()
        for tid in semantic_reads:
            read = f"{name}_read_{tid}"
            reads.append(read)
            lines += [
                f"    have {read} : {prior_text}.foldl (applyNodeDistributedFaithful {graph}) {store} {tid} = {store} {tid} := by",
                f"      exact foldl_applyNodeDistributedFaithful_at_not_written {graph} {prior_text} {store} {tid} (by native_decide) (by native_decide)",
            ]
        lines += [
            f"    have {name} : {final} {node.outs[0]} = {fn} {store} := by",
            "      calc",
            f"        {final} {node.outs[0]} = {fn} ({prior_text}.foldl (applyNodeDistributedFaithful {graph}) {store}) := by",
            f"          apply foldl_faithful_middle_writer {graph} {store} {prior_text} {tail_text} {node_text} {node.outs[0]} {fn}",
            "          · intro t",
            f"            exact applyNodeDistributedFaithful_zigzag_attn_out_two {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.ins[3]} {node.ins[4]} {node.outs[0]} {node.outs[1]} {params_text}",
            "          · native_decide",
            "          · native_decide",
        ]
        if prior:
            buddy_text = f"[{', '.join(_node_text(item) for item in nodes)}]"
            lines += [
                f"        _ = {fn} {store} := by",
                "          dsimp only",
                "          unfold applyNodeFaithfulZigzagAttnValue zigzagAttnUsesReplicatedKV",
                f"          rw [show {graph}.replicaBuddies {node_text} = {buddy_text} by native_decide]",
                "          simp only [List.map, List.all_cons, List.all_nil, Bool.and_true,",
                "            List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]",
                f"          rw [{', '.join(reads)}]",
            ]
        else:
            lines += ["        _ = _ := rfl"]
        return lines

    sm_graph, pm_graph = ir.sm_graph_ref, ir.pm_graph_ref
    causal = "true" if sm.params[4] != 0 else "false"
    lines = [
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {sm_graph} {pm_graph} {before.state_id} {after.state_id} where",
        f"  smNodes := [{sm_text}]", f"  pmNodes := [{p0_text}, {p1_text}]", "  sound := by",
        "    intro smStore pmStore hstate", f"    let smNodes : List NodeDecl := [{sm_text}]",
        f"    let pmNodes : List NodeDecl := [{p0_text}, {p1_text}]",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {sm_graph}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hq := hstate {q_rel.fact_id} (by native_decide)",
        f"    have hk := hstate {k_rel.fact_id} (by native_decide)",
        f"    have hv := hstate {v_rel.fact_id} (by native_decide)",
        f"    have hcuQ := hstate {cuq_cross.fact_id} (by native_decide)",
        f"    have hcuKV := hstate {cukv_cross.fact_id} (by native_decide)",
        f"    have hmetaAlias := hstate {meta_alias.fact_id} (by native_decide)",
        f"    have hcuQAlias := hstate {cuq_alias.fact_id} (by native_decide)",
        f"    have hpacked := hstate {packed.fact_id} (by native_decide)",
    ]
    lines += writer("hsm", sm_graph, "smStore", "smFinal", sm_nodes, 0)
    lines += writer("hp0", pm_graph, "pmStore", "pmFinal", pm_nodes, 0)
    lines += writer("hp1", pm_graph, "pmStore", "pmFinal", pm_nodes, 1)
    lines += [
        f"    change GeneratedPatterns.Zigzag2Rel (smStore {q_rel.sm_tid}) (pmStore {q_rel.pm_rank0_tid}) (pmStore {q_rel.pm_rank1_tid}) (pmStore {q_rel.metadata_tid}) {_shape_text(list(q_full))} {_shape_text(list(q_shard))} at hq",
        f"    change GeneratedPatterns.Ordinary2Rel (smStore {k_rel.sm_tid}) (pmStore {k_rel.pm_rank0_tid}) (pmStore {k_rel.pm_rank1_tid}) {_shape_text(list(k_full))} {_shape_text(list(k_shard))} at hk",
        f"    change GeneratedPatterns.Ordinary2Rel (smStore {v_rel.sm_tid}) (pmStore {v_rel.pm_rank0_tid}) (pmStore {v_rel.pm_rank1_tid}) {_shape_text(list(v_full))} {_shape_text(list(v_shard))} at hv",
        f"    change smStore {sm.ins[3]} = pmStore {p0.ins[3]} at hcuQ",
        f"    change smStore {sm.ins[4]} = pmStore {p0.ins[4]} at hcuKV",
        f"    change pmStore {q_rel.metadata_tid} = pmStore {packed.tid} at hmetaAlias",
        f"    change pmStore {p0.ins[3]} = pmStore {packed.tid} at hcuQAlias",
        f"    change ZigzagCollective.PackedCuSeqlensWF (pmStore {packed.tid}) {2 * l_dim} 2 at hpacked",
        "    have hcuAttn : pmStore " + str(p0.ins[3]) + " = pmStore " + str(q_rel.metadata_tid) + " := hcuQAlias.trans hmetaAlias.symm",
        "    have hdecoded : decodeCuSeqlens (pmStore " + str(q_rel.metadata_tid) + f") = [0, {2 * l_dim}] := by",
        "      rw [hmetaAlias]", "      exact hpacked.decoded_single",
        "    have hkGather := Ordinary2Rel.toGather2Rel hk (by native_decide)",
        "    have hvGather := Ordinary2Rel.toGather2Rel hv (by native_decide)",
        "    have hrel := GeneratedPatterns.Zigzag2Rel.attn_zigzag_sharded_kv",
        f"      (smStore {q_rel.sm_tid}) (pmStore {q_rel.pm_rank0_tid}) (pmStore {q_rel.pm_rank1_tid}) (pmStore {q_rel.metadata_tid})",
        f"      (smStore {k_rel.sm_tid}) (pmStore {k_rel.pm_rank0_tid}) (pmStore {k_rel.pm_rank1_tid})",
        f"      (smStore {v_rel.sm_tid}) (pmStore {v_rel.pm_rank0_tid}) (pmStore {v_rel.pm_rank1_tid})",
        f"      (pmStore {p0.ins[3]}) (pmStore {p0.ins[4]}) {l_dim} {q_heads} {kv_heads} {q_dim} {v_dim} {causal} {sm.params[5]}",
        "      hq hkGather hvGather hcuAttn hdecoded (by native_decide) (by native_decide)",
        "      (by native_decide) (by native_decide) (by native_decide)",
        f"    have hsmLower : applyNodeFaithfulZigzagAttnValue {sm_graph} smStore {sm_text} =",
        f"        fw_attn_varlen (smStore {sm.ins[0]}) (smStore {sm.ins[1]}) (smStore {sm.ins[2]}) (smStore {sm.ins[3]}) (smStore {sm.ins[4]}) {q_heads} {kv_heads} {q_dim} {v_dim} {causal} {sm.params[5]} := by",
        "      unfold applyNodeFaithfulZigzagAttnValue zigzagAttnUsesReplicatedKV",
        f"      rw [show {sm_graph}.replicaBuddies {sm_text} = [{sm_text}] by native_decide]",
        "      rfl",
        f"    have hp0Lower : applyNodeFaithfulZigzagAttnValue {pm_graph} pmStore {p0_text} =",
        f"        ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [pmStore {p0.ins[0]}, pmStore {p1.ins[0]}] [pmStore {p0.ins[1]}, pmStore {p1.ins[1]}] [pmStore {p0.ins[2]}, pmStore {p1.ins[2]}] (pmStore {p0.ins[3]}) (pmStore {p0.ins[4]}) {q_heads} {kv_heads} {q_dim} {v_dim} {causal} {sm.params[5]} 2 0 := by",
        "      unfold applyNodeFaithfulZigzagAttnValue zigzagAttnUsesReplicatedKV",
        f"      rw [show {pm_graph}.replicaBuddies {p0_text} = [{p0_text}, {p1_text}] by native_decide]",
        "      rfl",
        f"    have hp1Lower : applyNodeFaithfulZigzagAttnValue {pm_graph} pmStore {p1_text} =",
        f"        ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [pmStore {p0.ins[0]}, pmStore {p1.ins[0]}] [pmStore {p0.ins[1]}, pmStore {p1.ins[1]}] [pmStore {p0.ins[2]}, pmStore {p1.ins[2]}] (pmStore {p1.ins[3]}) (pmStore {p1.ins[4]}) {q_heads} {kv_heads} {q_dim} {v_dim} {causal} {sm.params[5]} 2 1 := by",
        "      unfold applyNodeFaithfulZigzagAttnValue zigzagAttnUsesReplicatedKV",
        f"      rw [show {pm_graph}.replicaBuddies {p1_text} = [{p0_text}, {p1_text}] by native_decide]",
        "      rfl",
        f"    have hout : {out_rel.fact_id}.Holds smFinal pmFinal := by",
        f"      change GeneratedPatterns.Zigzag2Rel (smFinal {out_rel.sm_tid}) (pmFinal {out_rel.pm_rank0_tid}) (pmFinal {out_rel.pm_rank1_tid}) (pmFinal {out_rel.metadata_tid}) {_shape_text(list(out_full))} {_shape_text(list(out_shard))}",
        "      have hmetadataFinal : pmFinal " + str(out_rel.metadata_tid) + " = pmStore " + str(out_rel.metadata_tid) + " := by",
        "        exact foldl_applyNodeDistributedFaithful_at_not_written " + pm_graph + " pmNodes pmStore " + str(out_rel.metadata_tid) + " (by native_decide) (by native_decide)",
        "      rw [hsm, hp0, hp1, hmetadataFinal]",
        "      dsimp only",
        "      rw [hsmLower, hp0Lower, hp1Lower, hcuQ, hcuKV]",
        "      rw [← hcuAttn]",
        "      exact hrel",
        "    exact RelationState.Holds.mono_insert hframe hout (by native_decide)",
    ]
    return "\n".join(lines) + "\n"


def render_closed_attention_segment(ir: GoalIR, relation,
                                    segment_id: str) -> str:
    """Render a closed ordinary sliding-window attention buddy segment."""
    chain = relation.dependent_chain_plan
    if chain is None:
        raise ValueError("closed dependent chain is unavailable")
    matches = [item for item in chain.segments if item.segment_id == segment_id]
    if len(matches) != 1:
        raise ValueError(f"expected one closed segment {segment_id}, found {len(matches)}")
    segment = matches[0]
    transitions = {item.transition_id: item for item in relation.transition_specs}
    if len(segment.transition_ids) != 1:
        raise ValueError(f"{segment_id} attention renderer requires one transition")
    transition = transitions[segment.transition_ids[0]]
    if transition.rule_id == "attention-zigzag-qkv-two-rank":
        return _render_closed_zigzag_attention_segment(ir, relation, segment_id)
    if transition.rule_id != "attention-ordinary-qkv-two-rank":
        raise ValueError(f"{segment_id} unsupported attention rule {transition.rule_id!r}")
    sm_nodes = ir.sm_nodes[segment.sm_range[0]:segment.sm_range[1]]
    pm_nodes = ir.pm_nodes[segment.pm_range[0]:segment.pm_range[1]]
    if len(sm_nodes) != 1 or len(pm_nodes) != 2:
        raise ValueError(f"{segment_id} attention requires one SM and two PM nodes")
    sm, p0, p1 = sm_nodes[0], pm_nodes[0], pm_nodes[1]
    if any(n.op != "FW_attn_sliding_window" for n in (sm, p0, p1)):
        raise ValueError(f"{segment_id} attention node family mismatch")
    if any(len(n.ins) != 5 or len(n.outs) != 2 for n in (sm, p0, p1)):
        raise ValueError(f"{segment_id} malformed attention signature")
    if sm.params != p0.params or p0.params != p1.params or len(sm.params) != 6:
        raise ValueError(f"{segment_id} attention params disagree")
    if p0.ins[3:] != p1.ins[3:]:
        raise ValueError(f"{segment_id} attention PM cu inputs disagree")
    facts = {fact.source: fact for fact in chain.relation_facts}
    pre = [facts[item] for item in transition.pre_facts]
    by_sm_tid = {fact.sm_tid: fact for fact in pre}
    try:
        q_rel, k_rel, v_rel = (by_sm_tid[sm.ins[i]] for i in range(3))
    except KeyError as exc:
        raise ValueError(f"{segment_id} missing attention input role {exc.args[0]}") from exc
    if any(f.kind != "ordinary" for f in (q_rel, k_rel, v_rel)):
        raise ValueError(f"{segment_id} ordinary attention requires ordinary q/k/v facts")
    out_rel = facts[transition.post_facts[0]]
    expected = [
        (q_rel.pm_rank0_tid, q_rel.pm_rank1_tid, p0.ins[0], p1.ins[0], "Q"),
        (k_rel.pm_rank0_tid, k_rel.pm_rank1_tid, p0.ins[1], p1.ins[1], "K"),
        (v_rel.pm_rank0_tid, v_rel.pm_rank1_tid, p0.ins[2], p1.ins[2], "V"),
        (out_rel.pm_rank0_tid, out_rel.pm_rank1_tid, p0.outs[0], p1.outs[0], "output"),
    ]
    for a, b, c, d, role in expected:
        if (a, b) != (c, d):
            raise ValueError(f"{segment_id} {role} role mismatch")
    if out_rel.kind != "ordinary" or out_rel.sm_tid != sm.outs[0]:
        raise ValueError(f"{segment_id} malformed attention output fact")

    def tensor_eq_fact(sm_tid: int, pm_tid: int):
        matches = []
        for fact in chain.authority_facts:
            if fact.kind != "tensor_eq":
                continue
            endpoints = {(fact.left_side, fact.left_tid), (fact.right_side, fact.right_tid)}
            if endpoints == {("sm", sm_tid), ("pm", pm_tid)}:
                matches.append(fact)
        if len(matches) != 1:
            raise ValueError(f"{segment_id} expected one tensor equality for SM {sm_tid}/PM {pm_tid}")
        return matches[0]

    cuq_fact, cuk_fact = tensor_eq_fact(sm.ins[3], p0.ins[3]), tensor_eq_fact(sm.ins[4], p0.ins[4])
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if not set(after.fact_ids).issubset(set(before.fact_ids) | {out_rel.fact_id}):
        raise ValueError(f"{segment_id} attention post-state contains unproved facts")
    l_dim, qh, qdim = q_rel.shard_shape
    _, kvh, kdim = k_rel.shard_shape
    _, vkvh, vdim = v_rel.shard_shape
    if kdim != qdim or vkvh != kvh or sm.params[:4] != [qh, kvh, qdim, vdim]:
        raise ValueError(f"{segment_id} attention shape/param mismatch")
    params_text = _shape_text(list(sm.params))
    sm_text, p0_text, p1_text = _node_text(sm), _node_text(p0), _node_text(p1)

    def writer(name: str, graph: str, store: str, final: str,
               nodes: list[Node], pos: int) -> list[str]:
        node = nodes[pos]
        prior, tail = nodes[:pos], nodes[pos + 1:]
        prior_text = f"[{', '.join(_node_text(item) for item in prior)}]"
        tail_text = f"[{', '.join(_node_text(item) for item in tail)}]"
        node_text = _node_text(node)
        fn = f"(fun t => applyNodeRingAttn_sliding_window {graph} t {node_text})"
        lines: list[str] = []
        reads: list[str] = []
        semantic_reads = tuple(dict.fromkeys(tid for buddy in nodes for tid in buddy.ins)) if prior else ()
        for tid in semantic_reads:
            read = f"{name}_read_{tid}"
            reads.append(read)
            lines += [
                f"    have {read} : {prior_text}.foldl (applyNodeDistributedFaithful {graph}) {store} {tid} = {store} {tid} := by",
                f"      exact foldl_applyNodeDistributedFaithful_at_not_written {graph} {prior_text} {store} {tid} (by native_decide) (by native_decide)",
            ]
        lines += [
            f"    have {name} : {final} {node.outs[0]} = {fn} {store} := by",
            "      calc",
            f"        {final} {node.outs[0]} = {fn} ({prior_text}.foldl (applyNodeDistributedFaithful {graph}) {store}) := by",
            f"          apply foldl_faithful_middle_writer {graph} {store} {prior_text} {tail_text} {node_text} {node.outs[0]} {fn}",
            "          · intro t",
            f"            exact applyNodeDistributedFaithful_sliding_attn_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.ins[3]} {node.ins[4]} {node.outs[0]} {node.outs[1]} {params_text}",
            "          · native_decide",
            "          · native_decide",
        ]
        if prior:
            buddy_text = f"[{', '.join(_node_text(item) for item in nodes)}]"
            lines += [
                f"        _ = {fn} {store} := by",
                "          dsimp only",
                "          unfold applyNodeRingAttn_sliding_window",
                f"          rw [show ringAttnBuddies {graph} {node_text} = {buddy_text} by native_decide]",
                "          simp only [List.map, List.getD, List.getElem?_cons_zero,",
                "            List.getElem?_cons_succ, Option.getD_some]",
                f"          rw [{', '.join(reads)}]",
            ]
        else:
            lines += ["        _ = _ := rfl"]
        return lines

    sm_graph, pm_graph = ir.sm_graph_ref, ir.pm_graph_ref
    lines = [
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {sm_graph} {pm_graph} {before.state_id} {after.state_id} where",
        f"  smNodes := [{sm_text}]", f"  pmNodes := [{p0_text}, {p1_text}]", "  sound := by",
        "    intro smStore pmStore hstate", f"    let smNodes : List NodeDecl := [{sm_text}]",
        f"    let pmNodes : List NodeDecl := [{p0_text}, {p1_text}]",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {sm_graph}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hq := hstate {q_rel.fact_id} (by native_decide)", f"    have hk := hstate {k_rel.fact_id} (by native_decide)",
        f"    have hv := hstate {v_rel.fact_id} (by native_decide)", f"    have hcuQ := hstate {cuq_fact.fact_id} (by native_decide)",
        f"    have hcuK := hstate {cuk_fact.fact_id} (by native_decide)",
    ]
    lines += writer("hsm", sm_graph, "smStore", "smFinal", sm_nodes, 0)
    lines += writer("hp0", pm_graph, "pmStore", "pmFinal", pm_nodes, 0)
    lines += writer("hp1", pm_graph, "pmStore", "pmFinal", pm_nodes, 1)
    lines += [
        f"    change GeneratedPatterns.Ordinary2Rel (smStore {q_rel.sm_tid}) (pmStore {q_rel.pm_rank0_tid}) (pmStore {q_rel.pm_rank1_tid}) {_shape_text(list(q_rel.full_shape))} {_shape_text(list(q_rel.shard_shape))} at hq",
        f"    change GeneratedPatterns.Ordinary2Rel (smStore {k_rel.sm_tid}) (pmStore {k_rel.pm_rank0_tid}) (pmStore {k_rel.pm_rank1_tid}) {_shape_text(list(k_rel.full_shape))} {_shape_text(list(k_rel.shard_shape))} at hk",
        f"    change GeneratedPatterns.Ordinary2Rel (smStore {v_rel.sm_tid}) (pmStore {v_rel.pm_rank0_tid}) (pmStore {v_rel.pm_rank1_tid}) {_shape_text(list(v_rel.full_shape))} {_shape_text(list(v_rel.shard_shape))} at hv",
        f"    change smStore {sm.ins[3]} = pmStore {p0.ins[3]} at hcuQ", f"    change smStore {sm.ins[4]} = pmStore {p0.ins[4]} at hcuK",
        f"    have hrel := Ordinary2Rel.sliding_attention {sm_graph} {pm_graph} smStore pmStore {sm_text} {p0_text} {p1_text}",
        f"      {l_dim} {qh} {kvh} {qdim} {vdim} {sm.params[4]} {sm.params[5]} hq hk hv hcuQ hcuK rfl rfl rfl rfl rfl",
        "      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
        "      (by native_decide) (by native_decide) (by native_decide)",
        f"    have hout : {out_rel.fact_id}.Holds smFinal pmFinal := by",
        f"      change GeneratedPatterns.Ordinary2Rel (smFinal {out_rel.sm_tid}) (pmFinal {out_rel.pm_rank0_tid}) (pmFinal {out_rel.pm_rank1_tid}) {_shape_text(list(out_rel.full_shape))} {_shape_text(list(out_rel.shard_shape))}",
        "      rw [hsm, hp0, hp1]", "      exact hrel",
        "    exact RelationState.Holds.mono_insert hframe hout (by native_decide)",
    ]
    return "\n".join(lines) + "\n"


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
    unary_adapters = {
        "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id": ("identity", "ordinary"),
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_id": ("identity", "zigzag"),
        "TrainVerify.Denote.fw_float_allGather0_commute_2": ("float", "ordinary"),
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.fw_float": ("float", "zigzag"),
        "TrainVerify.Denote.GeneratedPatterns.fw_view_allGather0_commute_cp2": ("flatten_3d", "ordinary"),
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_3d_to_2d": ("flatten_3d", "zigzag"),
    }
    adapter = unary_adapters.get(transition.lean_theorem)
    if adapter is None:
        raise ValueError("unary renderer received unsupported theorem")
    family, expected_kind = adapter
    if len(transition.pre_facts) != 1 or len(transition.post_facts) != 1:
        raise ValueError("unary renderer requires one pre/post fact")
    facts = {x.source: x for x in chain.relation_facts}
    pre, post = facts[transition.pre_facts[0]], facts[transition.post_facts[0]]
    if pre.kind != post.kind or pre.kind != expected_kind:
        raise ValueError("unary relation kind does not match theorem adapter")
    if family in ("identity", "float"):
        if (pre.full_shape, pre.shard_shape) != (post.full_shape, post.shard_shape):
            raise ValueError("identity unary changes relation shape")
    else:
        if len(pre.full_shape) != 3 or len(pre.shard_shape) != 3:
            raise ValueError("flatten-3d requires rank-3 inputs")
        l_dim, h_width, d_width = pre.shard_shape
        if min(l_dim, h_width, d_width) <= 0:
            raise ValueError("flatten-3d dimensions must be positive")
        if pre.full_shape != (2 * l_dim, h_width, d_width):
            raise ValueError("flatten-3d full input is not two ordered shards")
        if post.full_shape != (2 * l_dim, h_width * d_width) or post.shard_shape != (l_dim, h_width * d_width):
            raise ValueError("flatten-3d output does not merge the trailing axes")
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
    allowed_ops = {"flatten_3d": {"FW_reshape"}, "identity": {"FW_view", "FW_reshape"}, "float": {"FW_float"}}[family]
    if sm.op not in allowed_ops or any(n.op != sm.op for n in (p0, p1)):
        raise ValueError("unary operator does not match theorem adapter")
    if (sm.rank, p0.rank, p1.rank) != (0, 0, 1):
        raise ValueError("identity unary ranks are not ordered")
    if any(len(n.ins) != 1 or len(n.outs) != 1 for n in (sm, p0, p1)):
        raise ValueError("identity unary arity mismatch")
    if sm.op == "FW_float":
        if any(n.params for n in (sm, p0, p1)):
            raise ValueError("FW_float must have empty params")
    elif any(not n.params for n in (sm, p0, p1)) or tuple(sm.params) != post.full_shape or tuple(p0.params) != post.shard_shape or tuple(p1.params) != post.shard_shape:
        raise ValueError("unary target shapes mismatch")
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
    pre_full_shape = _shape_text(list(pre.full_shape)); pre_shard_shape = _shape_text(list(pre.shard_shape))
    post_full_shape = _shape_text(list(post.full_shape)); post_shard_shape = _shape_text(list(post.shard_shape))

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
    lines += out("hsm", "smGraph", "smStore", sm_nodes, 0, sm, "smFinal", post.full_shape)
    lines += out("hp0", "pmGraph", "pmStore", pm_nodes, 0, p0, "pmFinal", post.shard_shape)
    lines += out("hp1", "pmGraph", "pmStore", pm_nodes, 1, p1, "pmFinal", post.shard_shape)
    if pre.kind == "ordinary":
        lines += [f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change GeneratedPatterns.Ordinary2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) {post_full_shape} {post_shard_shape}",
            f"      change GeneratedPatterns.Ordinary2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) {pre_full_shape} {pre_shard_shape} at hin",
            "      rw [hsm, hp0, hp1]"]
        if family == "float":
            lines += ["      exact hin"]
        elif family == "identity":
            lines += ["      exact Ordinary2Rel.view_id hin"]
        else:
            lines += ["      refine ⟨?_, rfl, rfl, rfl⟩",
                "      rw [hin.full_value]",
                f"      exact GeneratedPatterns.fw_view_allGather0_commute_cp2 (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) {l_dim} {h_width} {d_width}",
                "        (by decide) (by decide) (by decide) hin.rank0_shape hin.rank1_shape"]
    else:
        lines += [f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change GeneratedPatterns.Zigzag2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) (pmFinal {post.metadata_tid}) {post_full_shape} {post_shard_shape}",
            f"      change GeneratedPatterns.Zigzag2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) (pmStore {pre.metadata_tid}) {pre_full_shape} {pre_shard_shape} at hin",
            f"      have hmeta : pmFinal {post.metadata_tid} = pmStore {pre.metadata_tid} := by",
            f"        exact foldl_applyNodeDistributedFaithful_at_not_written pmGraph pmNodes pmStore {pre.metadata_tid} (by native_decide) (by native_decide)",
            "      rw [hsm, hp0, hp1, hmeta]"]
        if family == "float":
            lines += ["      have hcore := GeneratedPatterns.Zigzag2Rel.fw_float 2 0 0 1 [] hin",
                "      simpa only [evalOp_fw_float, List.headD_cons] using hcore"]
        elif family == "identity":
            lines += ["      exact GeneratedPatterns.Zigzag2Rel.view_id' hin"]
        else:
            lines += [f"      exact GeneratedPatterns.Zigzag2Rel.view_3d_to_2d {l_dim} {h_width} {d_width} hin",
                "        (by decide) (by decide) (by decide)"]
    lines += ["    exact RelationState.Holds.mono_insert hframe hout (by native_decide)", ""]
    return "\n".join(lines)


def render_closed_full_producer_to_segment(ir: GoalIR, relation, segment_id: str) -> str:
    """Render one atomic zigzag full-producer plus ordinary FW_to component."""
    from .relation_compiler import FrontierToCertificate, FullProducerChunkCertificate

    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("full-producer/to renderer requires a complete closed chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None:
        raise ValueError(f"unknown full-producer/to segment: {segment_id}")
    transition_by_id = {item.transition_id: item for item in relation.transition_specs}
    transitions = [transition_by_id[item] for item in segment.transition_ids]
    full_transitions = [item for item in transitions if item.rule_id ==
        "FW_per_head_mix_precision_linear-full-producer-chunks-zigzag-two-rank"]
    to_transitions = [item for item in transitions if item.rule_id == "to-ordinary-two-rank"]
    if len(full_transitions) != 1 or not to_transitions or len(transitions) != 1 + len(to_transitions):
        raise ValueError("component is not one zigzag full-producer plus ordinary FW_to transitions")
    if full_transitions[0].lean_theorem != (
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.per_head_linear_fullProducer_chunks"
    ) or any(item.lean_theorem != "TrainVerify.Denote.fw_to_allGather0_commute_2"
             for item in to_transitions):
        raise ValueError("full-producer/to theorem family mismatch")

    records = {item.source: item for item in chain.relation_facts}
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    authority = {item.fact_id: item for item in chain.authority_facts}
    live_authority = [authority[item] for item in before.fact_ids if item in authority]
    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    sm_start, pm_start = segment.sm_range[0], segment.pm_range[0]
    if len(sm_nodes) != segment.sm_range[1] - segment.sm_range[0] or \
            len(pm_nodes) != segment.pm_range[1] - segment.pm_range[0]:
        raise ValueError("full-producer/to node slice is incomplete")
    sm_name = f"{segment.segment_id}_sm_nodes"
    pm_name = f"{segment.segment_id}_pm_nodes"
    sm_text = ", ".join(_node_text(item) for item in sm_nodes)
    pm_text = ", ".join(_node_text(item) for item in pm_nodes)

    def unique_authority(kind: str, predicate, label: str):
        matches = [item for item in live_authority if item.kind == kind and predicate(item)]
        if len(matches) != 1:
            raise ValueError(f"full-producer/to lacks unique live {label}")
        return matches[0]

    def exact_certificate(transition, cls):
        if len(transition.post_facts) != 1:
            raise ValueError("full-producer/to transition must have one post fact")
        post = records[transition.post_facts[0]]
        matches = [item for item in relation.certificates
                   if type(item) is cls and item.output_step_triple == post.source.step_triple]
        if len(matches) != 1:
            raise ValueError("full-producer/to transition lacks one exact certificate")
        return matches[0]

    writer_helpers: list[str] = []

    def unary_writer(name: str, side: str, absolute: int, node: Node, input_tid: int,
                     output_tid: int) -> list[str]:
        if side == "sm":
            graph, store, final, nodes_name, local = (
                ir.sm_graph_ref, "smStore", "smFinal", "smNodes", absolute - sm_start)
        elif side == "pm":
            graph, store, final, nodes_name, local = (
                ir.pm_graph_ref, "pmStore", "pmFinal", "pmNodes", absolute - pm_start)
        else:
            raise ValueError(f"unknown FW_to side: {side}")
        expr = f'(evalOp 2 0 "OpName.FW_to" [] [{store} {input_tid}]).headD (zeroTensor [])'
        helper_name = f"{segment.segment_id}_{name}"
        exact_nodes_name = sm_name if side == "sm" else pm_name
        writer_helpers.extend([
            f"private theorem {helper_name} ({store} : Store) :",
            f"    (({exact_nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {store}) {output_tid}) = {expr} := by",
            f"  let {nodes_name} : List NodeDecl := {exact_nodes_name}",
            f"  change ({nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {store}) {output_tid} = _",
            f"  rw [show {nodes_name} = {nodes_name}.take {local} ++ [{_node_text(node)}] ++ {nodes_name}.drop {local + 1} by native_decide]",
            f"  exact foldl_faithful_unary_middle_writer {graph} {store}",
            f"    ({nodes_name}.take {local}) ({nodes_name}.drop {local + 1}) {_node_text(node)}",
            f"    {input_tid} {output_tid} (fun x => (evalOp 2 0 \"OpName.FW_to\" [] [x]).headD (zeroTensor [])) (by",
            "      intro t",
            "      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "        (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "      simp [applyNodeDistributed, applyNodeRingAttn]",
            f"      rw [applyNode_fw_to_out {graph} t {node.rank} {input_tid} {output_tid} [], evalOp_fw_to]",
            "      rfl) (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
            "",
        ])
        return [
            f"    have {name} : {final} {output_tid} = {expr} := by",
            f"      simpa [{final}, {nodes_name}] using ({helper_name} {store})",
        ]

    full_transition = full_transitions[0]
    if len(full_transition.pre_facts) != 1 or len(full_transition.post_facts) != 1:
        raise ValueError("full-producer transition must have one pre/post fact")
    full_pre = records[full_transition.pre_facts[0]]
    full_post = records[full_transition.post_facts[0]]
    if full_pre.kind != "zigzag" or full_post.kind != "zigzag" or full_pre.metadata_tid is None or \
            (full_pre.metadata_tid, full_pre.metadata_region_id) != \
            (full_post.metadata_tid, full_post.metadata_region_id):
        raise ValueError("full-producer zigzag metadata provenance mismatch")
    full_cert = exact_certificate(full_transition, FullProducerChunkCertificate)
    if full_cert.relation_kind != "zigzag" or full_cert.pre_layout != "zigzag" or \
            full_cert.post_layout != "zigzag":
        raise ValueError("full-producer certificate is not zigzag")
    if len(full_transition.sm_node_indices) != 1 or len(full_transition.pm_node_indices) != 4:
        raise ValueError("full-producer footprint is not one SM plus gather/producer/chunks")
    sm_index = full_transition.sm_node_indices[0]
    sm_node = ir.sm_nodes[sm_index]
    gather_node, producer_node, chunk0_node, chunk1_node = (
        ir.pm_nodes[item] for item in full_transition.pm_node_indices)
    if sm_node.op != "FW_per_head_mix_precision_linear" or len(sm_node.ins) != 2 or \
            len(sm_node.outs) != 1 or sm_node.params:
        raise ValueError("full-producer SM signature mismatch")
    weight_tid = sm_node.ins[1]
    if full_cert.replicated_weight_binding != f"init:{weight_tid}" or \
            full_cert.weight_init_lineage_rank_tids != ((0, weight_tid),):
        raise ValueError("full-producer exact weight lineage mismatch")
    if (sm_node.ins[0], sm_node.outs[0]) != (full_pre.sm_tid, full_post.sm_tid):
        raise ValueError("full-producer SM roles do not match exact relation TIDs")
    if gather_node.op != "AllGatherPrim" or gather_node.params != [0] or \
            gather_node.rank != 0 or gather_node.ins != [full_pre.pm_rank0_tid, full_pre.pm_rank1_tid]:
        raise ValueError("full-producer gather roles/signature mismatch")
    if producer_node.op != sm_node.op or producer_node.ins != [gather_node.outs[0], weight_tid] or \
            producer_node.outs != sm_node.outs or producer_node.params:
        raise ValueError("full-producer PM producer mismatch")
    if (chunk0_node.op, chunk1_node.op, chunk0_node.rank, chunk1_node.rank,
            chunk0_node.params, chunk1_node.params) != (
            "ChunkPrim", "ChunkPrim", 0, 1, [0], [0]):
        raise ValueError("full-producer chunks are not ordered dim-0 rank chunks")
    if chunk0_node.ins != producer_node.outs or chunk1_node.ins != producer_node.outs or \
            (chunk0_node.outs[0], chunk1_node.outs[0]) != \
            (full_post.pm_rank0_tid, full_post.pm_rank1_tid):
        raise ValueError("full-producer chunk roles do not match exact post TIDs")
    if len(full_pre.full_shape) != 2 or len(full_pre.shard_shape) != 2 or \
            len(full_post.full_shape) != 3 or len(full_post.shard_shape) != 3:
        raise ValueError("full-producer shape ranks mismatch")
    ldim, k = full_pre.shard_shape
    hdim, ddim = full_post.shard_shape[1:]
    if full_pre.full_shape != (2 * ldim, k) or full_post.full_shape != (2 * ldim, hdim, ddim) or \
            full_post.shard_shape != (ldim, hdim, ddim):
        raise ValueError("full-producer exact shapes mismatch")
    weight_shape = (hdim, ddim, k)
    weight_eq = unique_authority(
        "tensor_eq", lambda item: (item.left_side, item.left_tid, item.right_side, item.right_tid)
        == ("sm", weight_tid, "pm", weight_tid), f"weight equality {weight_tid}")
    weight_shape_fact = unique_authority(
        "tensor_shape", lambda item: (item.side, item.tid, item.shape)
        == ("pm", weight_tid, weight_shape), f"weight shape {weight_tid}")
    metadata_eq = unique_authority(
        "tensor_eq", lambda item: item.left_side == "pm" and item.left_tid == full_pre.metadata_tid
        and item.right_side == "pm", f"metadata equality {full_pre.metadata_tid}")
    packed = unique_authority(
        "packed_cu", lambda item: item.side == "pm" and item.tid == metadata_eq.right_tid
        and item.total_tokens == full_pre.full_shape[0] and item.num_ranks == 2,
        f"packed metadata {full_pre.metadata_tid}")
    required = {full_pre.fact_id, weight_eq.fact_id, weight_shape_fact.fact_id,
                metadata_eq.fact_id, packed.fact_id}
    if not required <= set(before.fact_ids):
        raise ValueError("full-producer exact relation/weight/packed authority is not live")

    to_rows = []
    for number, transition in enumerate(to_transitions, 1):
        if len(transition.pre_facts) != 1 or len(transition.post_facts) != 1 or \
                len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != 2:
            raise ValueError("FW_to transition footprint/facts mismatch")
        cert = exact_certificate(transition, FrontierToCertificate)
        pre = records[transition.pre_facts[0]]
        post = records[transition.post_facts[0]]
        if cert.relation_kind != "ordinary" or pre.kind != "ordinary" or post.kind != "ordinary" or \
                (pre.full_shape, pre.shard_shape) != (post.full_shape, post.shard_shape) or \
                cert.input_shape != pre.full_shape or cert.output_shape != post.full_shape:
            raise ValueError("FW_to exact relation/shape mismatch")
        smi = transition.sm_node_indices[0]
        pmi0, pmi1 = transition.pm_node_indices
        sm, pm0, pm1 = ir.sm_nodes[smi], ir.pm_nodes[pmi0], ir.pm_nodes[pmi1]
        if any(item.op != "FW_to" or len(item.ins) != 1 or len(item.outs) != 1 or item.params
               for item in (sm, pm0, pm1)) or (sm.rank, pm0.rank, pm1.rank) != (0, 0, 1):
            raise ValueError("FW_to exact node signatures/ranks mismatch")
        if (sm.ins[0], pm0.ins[0], pm1.ins[0]) != \
                (pre.sm_tid, pre.pm_rank0_tid, pre.pm_rank1_tid):
            raise ValueError("FW_to input roles do not match exact node TIDs")
        if (sm.outs[0], pm0.outs[0], pm1.outs[0]) != \
                (post.sm_tid, post.pm_rank0_tid, post.pm_rank1_tid):
            raise ValueError("FW_to output roles do not match exact node TIDs")
        if pre.fact_id not in before.fact_ids:
            raise ValueError("FW_to exact input fact is not live")
        to_rows.append((number, transition, pre, post, smi, pmi0, pmi1, sm, pm0, pm1))

    fresh = [full_post] + [row[3] for row in to_rows]
    if len({item.fact_id for item in fresh}) != len(fresh):
        raise ValueError("full-producer/to has duplicate post facts")
    if not set(after.fact_ids) <= (set(before.fact_ids) | {item.fact_id for item in fresh}):
        raise ValueError("full-producer/to post-state introduces unproved facts")

    lines = [
        f"private def {sm_name} : List NodeDecl := [{sm_text}]",
        f"private def {pm_name} : List NodeDecl := [{pm_text}]", "",
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_name}", f"  pmNodes := {pm_name}", "  sound := by",
        "    intro smStore pmStore hstate", f"    let smNodes : List NodeDecl := {sm_name}",
        f"    let pmNodes : List NodeDecl := {pm_name}",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hFullIn : {full_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hWeightEq : {weight_eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hWeightShape : {weight_shape_fact.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hMetadataEq : pmFinal {full_pre.metadata_tid} = pmFinal {metadata_eq.right_tid} := by",
        f"      simpa [{metadata_eq.fact_id}, RelationFact.Holds, StoreSide.read] using (hframe _ (by native_decide : {metadata_eq.fact_id} ∈ {before.state_id}.facts))",
        f"    have hPacked : ZigzagCollective.PackedCuSeqlensWF (pmFinal {metadata_eq.right_tid}) {packed.total_tokens} 2 := by",
        f"      simpa [{packed.fact_id}, RelationFact.Holds, StoreSide.read] using (hframe _ (by native_decide : {packed.fact_id} ∈ {before.state_id}.facts))",
        f"    have hDecoded : decodeCuSeqlens (pmFinal {full_pre.metadata_tid}) = [0, {packed.total_tokens}] := by",
        "      rw [hMetadataEq]", "      exact hPacked.decoded_single",
    ]

    sm_pos = sm_index - sm_start
    lines += [
        f"    have hFullSm : smFinal {sm_node.outs[0]} = fw_per_head_linear (smStore {sm_node.ins[0]}) (smStore {weight_tid}) := by",
        f"      change (smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore) {sm_node.outs[0]} = _",
        f"      rw [show smNodes = smNodes.take {sm_pos} ++ [{_node_text(sm_node)}] ++ smNodes.drop {sm_pos + 1} by native_decide]",
        f"      exact foldl_faithful_binary_middle_writer {ir.sm_graph_ref} smStore",
        f"        (smNodes.take {sm_pos}) (smNodes.drop {sm_pos + 1}) {_node_text(sm_node)}",
        f"        {sm_node.ins[0]} {weight_tid} {sm_node.outs[0]} (fun x w => fw_per_head_linear x w) (by",
        "          intro t", "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
        "          simp [applyNodeDistributed, applyNodeRingAttn]",
        f"          exact applyNode_fw_per_head_mix_precision_linear_out {ir.sm_graph_ref} t {sm_node.rank} {sm_node.ins[0]} {weight_tid} {sm_node.outs[0]} [])",
        "        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
    ]
    gather_pos, producer_pos, chunk0_pos, chunk1_pos = (
        item - pm_start for item in full_transition.pm_node_indices)
    lines += [
        f"    let pmBeforeProducer := (pmNodes.take {producer_pos}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hGather : pmBeforeProducer {gather_node.outs[0]} = allGatherPrimDimN 0 2 0 [pmStore {gather_node.ins[0]}, pmStore {gather_node.ins[1]}] := by",
        "      change ((pmNodes.take " + str(producer_pos) + f").foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {gather_node.outs[0]} = _",
        f"      rw [show pmNodes.take {producer_pos} = (pmNodes.take {producer_pos}).take {gather_pos} ++ [{_node_text(gather_node)}] ++ (pmNodes.take {producer_pos}).drop {gather_pos + 1} by native_decide]",
        f"      exact foldl_faithful_binary_middle_writer {ir.pm_graph_ref} pmStore",
        f"        ((pmNodes.take {producer_pos}).take {gather_pos}) ((pmNodes.take {producer_pos}).drop {gather_pos + 1}) {_node_text(gather_node)}",
        f"        {gather_node.ins[0]} {gather_node.ins[1]} {gather_node.outs[0]} (fun x y => allGatherPrimDimN 0 2 0 [x, y]) (by",
        "          intro t", "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
        "          simp [applyNodeDistributed, applyNodeRingAttn]",
        f"          rw [applyNode_allGatherPrimDimN_out {ir.pm_graph_ref} t 0 [{gather_node.ins[0]}, {gather_node.ins[1]}] {gather_node.outs[0]} 0]",
        f"          rw [show {ir.pm_graph_ref}.numRanks = 2 by rfl]", "          rfl)",
        "        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
        f"    have hWeightBefore : pmBeforeProducer {weight_tid} = pmStore {weight_tid} := by",
        f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} (pmNodes.take {producer_pos}) pmStore {weight_tid} (by native_decide) (by native_decide)",
    ]
    for rank, (chunk_node, chunk_pos) in enumerate(((chunk0_node, chunk0_pos), (chunk1_node, chunk1_pos))):
        lines += [
            f"    let pmBeforeChunk{rank} := (pmNodes.take {chunk_pos}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
            f"    have hProducer{rank} : pmBeforeChunk{rank} {producer_node.outs[0]} = fw_per_head_linear (allGatherPrimDimN 0 2 0 [pmStore {gather_node.ins[0]}, pmStore {gather_node.ins[1]}]) (pmStore {weight_tid}) := by",
            f"      rw [show pmBeforeChunk{rank} {producer_node.outs[0]} = fw_per_head_linear (pmBeforeProducer {producer_node.ins[0]}) (pmBeforeProducer {producer_node.ins[1]}) by",
            f"        change ((pmNodes.take {chunk_pos}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {producer_node.outs[0]} = _",
            f"        rw [show pmNodes.take {chunk_pos} = pmNodes.take {producer_pos} ++ [{_node_text(producer_node)}] ++ (pmNodes.take {chunk_pos}).drop {producer_pos + 1} by native_decide]",
            f"        exact foldl_faithful_binary_writer {ir.pm_graph_ref} pmStore (pmNodes.take {producer_pos}) ((pmNodes.take {chunk_pos}).drop {producer_pos + 1}) {_node_text(producer_node)}",
            f"          {producer_node.ins[0]} {producer_node.ins[1]} {producer_node.outs[0]} (fun x w => fw_per_head_linear x w) (by",
            "            intro t", "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "            simp [applyNodeDistributed, applyNodeRingAttn]",
            f"            exact applyNode_fw_per_head_mix_precision_linear_out {ir.pm_graph_ref} t {producer_node.rank} {producer_node.ins[0]} {weight_tid} {producer_node.outs[0]} [])",
            "          (by native_decide) (by native_decide)]", "      rw [hGather, hWeightBefore]",
            f"    have hChunk{rank} : pmFinal {chunk_node.outs[0]} = chunkPrimDimN 0 2 {rank} (pmBeforeChunk{rank} {producer_node.outs[0]}) := by",
            f"      change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {chunk_node.outs[0]} = _",
            f"      rw [show pmNodes = pmNodes.take {chunk_pos} ++ [{_node_text(chunk_node)}] ++ pmNodes.drop {chunk_pos + 1} by native_decide]",
            f"      exact foldl_faithful_chunk_writer {ir.pm_graph_ref} pmStore (pmNodes.take {chunk_pos}) (pmNodes.drop {chunk_pos + 1}) {rank}",
            f"        {producer_node.outs[0]} {chunk_node.outs[0]} 0 rfl (by native_decide) (by native_decide)",
        ]
    lines += [
        f"    have hMetadataFinal : pmFinal {full_pre.metadata_tid} = pmStore {full_pre.metadata_tid} := by",
        f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore {full_pre.metadata_tid} (by native_decide) (by native_decide)",
        f"    have hout0 : {full_post.fact_id}.Holds smFinal pmFinal := by",
        f"      change GeneratedPatterns.Zigzag2Rel (smFinal {full_post.sm_tid}) (pmFinal {full_post.pm_rank0_tid}) (pmFinal {full_post.pm_rank1_tid}) (pmFinal {full_post.metadata_tid}) {_shape_text(list(full_post.full_shape))} {_shape_text(list(full_post.shard_shape))}",
        f"      change GeneratedPatterns.Zigzag2Rel (smStore {full_pre.sm_tid}) (pmStore {full_pre.pm_rank0_tid}) (pmStore {full_pre.pm_rank1_tid}) (pmStore {full_pre.metadata_tid}) {_shape_text(list(full_pre.full_shape))} {_shape_text(list(full_pre.shard_shape))} at hFullIn",
        f"      change smStore {weight_tid} = pmStore {weight_tid} at hWeightEq",
        f"      change (pmStore {weight_tid}).shape = {_shape_text(list(weight_shape))} at hWeightShape",
        "      rw [hMetadataFinal]",
        f"      exact GeneratedPatterns.Zigzag2Rel.per_head_linear_fullProducer_chunks {ldim} {k} {hdim} {ddim}",
        "        hFullIn hWeightShape hWeightEq hFullSm hGather hProducer0 hChunk0",
        f"        (calc pmFinal {chunk1_node.outs[0]} = chunkPrimDimN 0 2 1 (pmBeforeChunk1 {producer_node.outs[0]}) := hChunk1",
        f"          _ = chunkPrimDimN 0 2 1 (pmBeforeChunk0 {producer_node.outs[0]}) := congrArg (chunkPrimDimN 0 2 1) (hProducer1.trans hProducer0.symm))",
        "        (by decide) (by decide) (by decide) (by decide)",
    ]

    for number, transition, pre, post, smi, pmi0, pmi1, sm, pm0, pm1 in to_rows:
        lines += [f"    have hToIn{number} : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)"]
        lines += unary_writer(f"hToSm{number}", "sm", smi, sm, sm.ins[0], sm.outs[0])
        lines += unary_writer(f"hToPm{number}_0", "pm", pmi0, pm0, pm0.ins[0], pm0.outs[0])
        lines += unary_writer(f"hToPm{number}_1", "pm", pmi1, pm1, pm1.ins[0], pm1.outs[0])
        full_shape, shard_shape = _shape_text(list(post.full_shape)), _shape_text(list(post.shard_shape))
        lines += [
            f"    have hout{number} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change GeneratedPatterns.Ordinary2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) {full_shape} {shard_shape}",
            f"      change GeneratedPatterns.Ordinary2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) {full_shape} {shard_shape} at hToIn{number}",
            f"      rw [hToSm{number}, hToPm{number}_0, hToPm{number}_1]",
            "      refine ⟨?_, ?_, ?_, ?_⟩",
            f"      · rw [hToIn{number}.full_value]",
            f"        exact fw_to_allGather0_commute_2 2 0 [] (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid})",
            f"      · simpa only [evalOp_fw_to, List.headD_cons] using hToIn{number}.full_shape",
            f"      · simpa only [evalOp_fw_to, List.headD_cons] using hToIn{number}.rank0_shape",
            f"      · simpa only [evalOp_fw_to, List.headD_cons] using hToIn{number}.rank1_shape",
        ]
    fresh_ids = [item.fact_id for item in fresh]
    lines += [
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with " + " | ".join("rfl" for _ in fresh),
    ]
    lines += [f"      · exact hout{index}" for index in range(len(fresh))]
    lines += ["    · exact hframe fact old", ""]
    lines = lines[:3] + writer_helpers + lines[3:]
    return "\n".join(lines)


def render_closed_linear_segment(ir: GoalIR, relation, segment_id: str) -> str:
    from .relation_compiler import (
        FrontierLinearCertificate,
        FrontierRMSNormCertificate,
        FullProducerChunkCertificate,
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
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.rms_norm",
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
        elif op == "FW_rms_norm":
            conclusion = f"exact applyNode_fw_rms_norm_out_1p {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}"
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
        FrontierLinearCertificate, FrontierRMSNormCertificate,
        FullProducerChunkCertificate, PerHeadLinearRelationCertificate,
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
        if len(transition.sm_node_indices) != 1:
            raise ValueError("atomic linear/RMS transition must own one SM node")
        sm_idx = transition.sm_node_indices[0]
        sm = ir.sm_nodes[sm_idx]
        if len(sm.ins) != 2 or len(sm.outs) != 1 or sm.params:
            raise ValueError("SM linear/RMS signature mismatch")
        weight_tid = sm.ins[1]
        if type(cert) is FrontierRMSNormCertificate:
            if transition.rule_id != "rms-norm-zigzag-two-rank" or sm.op != "FW_rms_norm":
                raise ValueError("zigzag RMSNorm certificate/operator mismatch")
            if cert.replicated_weight_tid != weight_tid:
                raise ValueError("zigzag RMSNorm certificate weight binding mismatch")
            if len(transition.pm_node_indices) != 2:
                raise ValueError("zigzag RMSNorm footprint is not 1x2")
            p0i, p1i = transition.pm_node_indices
            p0, p1 = ir.pm_nodes[p0i], ir.pm_nodes[p1i]
            nodes = (sm, p0, p1)
            if any(n.op != "FW_rms_norm" or n.params or len(n.ins) != 2 or len(n.outs) != 1 for n in nodes):
                raise ValueError("zigzag RMSNorm node signature mismatch")
            if (sm.rank, p0.rank, p1.rank) != (0, 0, 1):
                raise ValueError("zigzag RMSNorm ranks are not ordered")
            if {n.ins[1] for n in nodes} != {weight_tid}:
                raise ValueError("zigzag RMSNorm weight is not exactly replicated")
            if (pre.kind, post.kind) != ("zigzag", "zigzag"):
                raise ValueError("zigzag RMSNorm relation kind mismatch")
            if (pre.metadata_tid is None or pre.metadata_tid != post.metadata_tid or
                    pre.metadata_region_id != post.metadata_region_id):
                raise ValueError("zigzag RMSNorm metadata provenance mismatch")
            if (pre.full_shape, pre.shard_shape) != (post.full_shape, post.shard_shape):
                raise ValueError("zigzag RMSNorm changes relation shapes")
            if len(pre.shard_shape) != 2 or pre.full_shape != (pre.shard_shape[0] * 2, pre.shard_shape[1]):
                raise ValueError("zigzag RMSNorm requires exact two-rank 2D shapes")
            if any(dim <= 0 for dim in pre.shard_shape):
                raise ValueError("zigzag RMSNorm dimensions must be positive")
            expected_inputs = (pre.sm_tid, pre.pm_rank0_tid, pre.pm_rank1_tid)
            expected_outputs = (post.sm_tid, post.pm_rank0_tid, post.pm_rank1_tid)
            if tuple(n.ins[0] for n in nodes) != expected_inputs or tuple(n.outs[0] for n in nodes) != expected_outputs:
                raise ValueError("zigzag RMSNorm fact roles do not match actual node TIDs")
            eqs = [x for x in live_authority if x.kind == "tensor_eq" and
                   (x.left_side, x.left_tid, x.right_side, x.right_tid) ==
                   ("sm", weight_tid, "pm", weight_tid)]
            if len(eqs) != 1:
                raise ValueError("zigzag RMSNorm lacks unique live replicated weight authority")
            eq = eqs[0]
            lines += [
                f"    have hin{number} : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
                f"    have hwEq{number} : {eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            ]
            lines += binary_middle(f"hSm{number}", ir.sm_graph_ref, "smStore", sm_slice,
                                   sm_idx - sm_start, sm, "smFinal", "fw_rms_norm {x} {w}")
            lines += binary_middle(f"hPm{number}_0", ir.pm_graph_ref, "pmStore", pm_slice,
                                   p0i - pm_start, p0, "pmFinal", "fw_rms_norm {x} {w}")
            lines += binary_middle(f"hPm{number}_1", ir.pm_graph_ref, "pmStore", pm_slice,
                                   p1i - pm_start, p1, "pmFinal", "fw_rms_norm {x} {w}")
            shard, hidden = pre.shard_shape
            lines += [
                f"    have hmeta{number} : pmFinal {post.metadata_tid} = pmStore {pre.metadata_tid} := by",
                f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore {pre.metadata_tid} (by native_decide) (by native_decide)",
                f"    have hout{number} : {post.fact_id}.Holds smFinal pmFinal := by",
                f"      change GeneratedPatterns.Zigzag2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) (pmStore {pre.metadata_tid}) {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))} at hin{number}",
                f"      change smStore {weight_tid} = pmStore {weight_tid} at hwEq{number}",
                f"      change GeneratedPatterns.Zigzag2Rel (smFinal {post.sm_tid}) (pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) (pmFinal {post.metadata_tid}) {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
                f"      rw [hSm{number}, hPm{number}_0, hPm{number}_1, hmeta{number}, hwEq{number}]",
                f"      exact GeneratedPatterns.Zigzag2Rel.rms_norm {shard} {hidden} hin{number} (by decide) (by decide) rfl",
            ]
            continue
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
        if not isinstance(cert, (FullProducerChunkCertificate, PerHeadLinearRelationCertificate)):
            raise TypeError("unsupported exact per-head linear certificate class")
        if getattr(cert, "replicated_weight_tid", weight_tid) != weight_tid:
            raise ValueError("per-head linear certificate weight binding mismatch")
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
            if (sm.ins[0], p0.ins[0], p1.ins[0]) != (pre.sm_tid, pre.pm_rank0_tid, pre.pm_rank1_tid):
                raise ValueError("local per-head linear input roles do not match actual node TIDs")
            if (sm.outs[0], p0.outs[0], p1.outs[0]) != (post.sm_tid, post.pm_rank0_tid, post.pm_rank1_tid):
                raise ValueError("local per-head linear output roles do not match actual node TIDs")
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


def render_closed_rms_shuffle_segment(ir: GoalIR, relation, segment_id: str) -> str:
    """Render one atomic ordinary RMSNorm plus faithful shuffle component."""
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("RMSNorm+shuffle segment requires a complete closed chain")
    segment = next((x for x in chain.segments if x.segment_id == segment_id), None)
    if segment is None:
        raise ValueError(f"unknown RMSNorm+shuffle segment: {segment_id}")
    by_id = {x.transition_id: x for x in relation.transition_specs}
    transitions = [by_id[x] for x in segment.transition_ids]
    family = tuple(x.rule_id for x in transitions)
    expected = (
        "rms-norm-ordinary-two-rank",
        "faithful-maybe-shuffle-ordinary-to-zigzag-two-rank",
    )
    if family != expected:
        raise ValueError("segment is not the registered atomic RMSNorm+shuffle family")
    rms, shuffle = transitions
    if rms.lean_theorem != "TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core":
        raise ValueError("RMSNorm theorem key mismatch")
    if shuffle.lean_theorem != "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.of_sources":
        raise ValueError("shuffle theorem key mismatch")

    sms = ir.sm_nodes[slice(*segment.sm_range)]
    pms = ir.pm_nodes[slice(*segment.pm_range)]
    if len(sms) != 2 or len(pms) != 4:
        raise ValueError("RMSNorm+shuffle footprint mismatch")
    sm_rms, sm_shuffle = sms
    pm_rms0, pm_shuffle0, pm_rms1, pm_shuffle1 = pms
    rms_nodes = (sm_rms, pm_rms0, pm_rms1)
    shuffle_nodes = (sm_shuffle, pm_shuffle0, pm_shuffle1)
    if any(
        x.op != "FW_rms_norm"
        or len(x.ins) != 2
        or len(x.outs) != 1
        or x.params not in (None, [])
        for x in rms_nodes
    ):
        raise ValueError("RMSNorm signature/params mismatch")
    if any(
        x.op != "FW_maybe_shuffle" or len(x.ins) != 2 or len(x.outs) != 1
        for x in shuffle_nodes
    ) or tuple(x.params for x in shuffle_nodes) != ([1, 0], [2, 0], [2, 1]):
        raise ValueError("shuffle signature/params mismatch")
    if tuple(x.rank for x in rms_nodes) != (0, 0, 1) or tuple(
        x.rank for x in shuffle_nodes
    ) != (0, 0, 1):
        raise ValueError("RMSNorm+shuffle rank mismatch")
    if rms.sm_node_indices != (segment.sm_range[0],) or rms.pm_node_indices != (
        segment.pm_range[0], segment.pm_range[0] + 2
    ):
        raise ValueError("RMSNorm authority footprint mismatch")
    if shuffle.sm_node_indices != (segment.sm_range[0] + 1,) or shuffle.pm_node_indices != (
        segment.pm_range[0] + 1, segment.pm_range[0] + 3
    ):
        raise ValueError("shuffle authority footprint mismatch")

    records = {x.source: x for x in chain.relation_facts}
    rms_pre, rms_post = records[rms.pre_facts[0]], records[rms.post_facts[0]]
    shuffle_pre, shuffle_post = records[shuffle.pre_facts[0]], records[shuffle.post_facts[0]]
    if any(x.kind != "ordinary" for x in (rms_pre, rms_post, shuffle_pre)) or shuffle_post.kind != "zigzag":
        raise ValueError("RMSNorm+shuffle relation kinds mismatch")
    for fact, nodes, outputs in (
        (rms_pre, rms_nodes, False),
        (rms_post, rms_nodes, True),
        (shuffle_pre, shuffle_nodes, False),
        (shuffle_post, shuffle_nodes, True),
    ):
        tids = tuple(x.outs[0] if outputs else x.ins[0] for x in nodes)
        if tids != (fact.sm_tid, fact.pm_rank0_tid, fact.pm_rank1_tid):
            raise ValueError("RMSNorm+shuffle fact roles do not match node TIDs")
    if rms_pre.full_shape != rms_post.full_shape or rms_pre.shard_shape != rms_post.shard_shape:
        raise ValueError("RMSNorm relation payload mismatch")
    if shuffle_pre.full_shape != shuffle_post.full_shape or shuffle_pre.shard_shape != shuffle_post.shard_shape:
        raise ValueError("shuffle relation payload mismatch")
    if any(
        len(x.shard_shape) != 2
        or x.full_shape != (x.shard_shape[0] * 2, x.shard_shape[1])
        for x in (rms_pre, shuffle_pre)
    ):
        raise ValueError("RMSNorm+shuffle shape is not positive two-rank 2D")
    if any(dim <= 0 for fact in (rms_pre, shuffle_pre) for dim in fact.shard_shape):
        raise ValueError("RMSNorm+shuffle shape is not positive two-rank 2D")
    weights = {x.ins[1] for x in rms_nodes}
    metadata = {x.ins[1] for x in shuffle_nodes}
    if len(weights) != 1 or len(metadata) != 1:
        raise ValueError("RMSNorm weight or shuffle metadata binding mismatch")
    weight = next(iter(weights)); metadata_tid = next(iter(metadata))
    if shuffle_post.metadata_tid != metadata_tid or shuffle_post.metadata_region_id is None:
        raise ValueError("shuffle metadata provenance mismatch")

    authorities = list(chain.authority_facts)
    weight_facts = [
        x for x in authorities
        if x.kind == "tensor_eq" and (x.left_side, x.left_tid, x.right_side, x.right_tid)
        == ("sm", weight, "pm", weight)
    ]
    metadata_aliases = [
        x for x in authorities
        if x.kind == "tensor_eq" and (x.left_side, x.left_tid) == ("pm", metadata_tid)
        and x.right_side == "pm"
    ]
    if len(weight_facts) != 1 or len(metadata_aliases) != 1:
        raise ValueError("RMSNorm weight or shuffle metadata equality authority mismatch")
    metadata_alias = metadata_aliases[0]
    packed_facts = [
        x for x in authorities
        if x.kind == "packed_cu" and (x.side, x.tid, x.num_ranks)
        == ("pm", metadata_alias.right_tid, 2)
    ]
    if len(packed_facts) != 1:
        raise ValueError("shuffle PackedCuSeqlensWF authority mismatch")
    packed = packed_facts[0]
    if packed.total_tokens != shuffle_pre.shard_shape[0] * 2:
        raise ValueError("shuffle packed-cu token count mismatch")

    states = {x.state_id: x for x in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {
        rms_pre.fact_id, shuffle_pre.fact_id, weight_facts[0].fact_id,
        metadata_alias.fact_id, packed.fact_id,
    }
    if not required <= set(before.fact_ids):
        raise ValueError("RMSNorm+shuffle authority is not live in the pre-state")
    fresh = {rms_post.fact_id, shuffle_post.fact_id}
    if not fresh <= set(after.fact_ids) or not set(after.fact_ids) <= fresh | set(before.fact_ids):
        raise ValueError("RMSNorm+shuffle state delta mismatch")

    sm_text = [_node_text(x) for x in sms]
    pm_text = [_node_text(x) for x in pms]
    fs_rms, ss_rms = _shape_text(rms_post.full_shape), _shape_text(rms_post.shard_shape)
    fs_shuf, ss_shuf = _shape_text(shuffle_post.full_shape), _shape_text(shuffle_post.shard_shape)
    shard_rms, hidden_rms = rms_pre.shard_shape
    sm_graph, pm_graph = ir.sm_graph_ref, ir.pm_graph_ref

    lines = [
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {sm_graph} {pm_graph} {before.state_id} {after.state_id} where",
        f"  smNodes := [{', '.join(sm_text)}]",
        f"  pmNodes := [{', '.join(pm_text)}]",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := [{', '.join(sm_text)}]",
        f"    let pmNodes : List NodeDecl := [{', '.join(pm_text)}]",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {sm_graph}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hRmsIn : {rms_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hShuffleIn : {shuffle_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hWeight : {weight_facts[0].fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hPacked : {packed.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hMetadataAlias : {metadata_alias.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    change smStore {weight} = pmStore {weight} at hWeight",
        f"    change ZigzagCollective.PackedCuSeqlensWF (pmStore {packed.tid}) {packed.total_tokens} 2 at hPacked",
        f"    change pmStore {metadata_tid} = pmStore {packed.tid} at hMetadataAlias",
        f"    have hPackedActual : ZigzagCollective.PackedCuSeqlensWF (pmStore {metadata_tid}) {packed.total_tokens} 2 := by",
        "      rw [hMetadataAlias]", "      exact hPacked",
    ]

    def rms_writer(name, graph, store, final, node, before_nodes, after_nodes):
        return [
            f"    have {name} : {final} {node.outs[0]} = fw_rms_norm ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",
            f"      simpa [{final}, {'smNodes' if final == 'smFinal' else 'pmNodes'}] using",
            f"        (foldl_faithful_binary_middle_writer {graph} {store}",
            f"          [{', '.join(_node_text(x) for x in before_nodes)}] [{', '.join(_node_text(x) for x in after_nodes)}] {_node_text(node)}",
            f"          {node.ins[0]} {node.ins[1]} {node.outs[0]} fw_rms_norm (by",
            "            intro t",
            "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "            simp [applyNodeDistributed, applyNodeRingAttn]",
            f"            exact applyNode_fw_rms_norm_out_1p {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]})",
            "          (by native_decide) (by native_decide) (by native_decide)",
            "          (by native_decide) (by native_decide))",
        ]

    lines += rms_writer("hSmRms", sm_graph, "smStore", "smFinal", sm_rms, [], [sm_shuffle])
    lines += rms_writer("hPmRms0", pm_graph, "pmStore", "pmFinal", pm_rms0, [], pms[1:])
    lines += rms_writer("hPmRms1", pm_graph, "pmStore", "pmFinal", pm_rms1, pms[:2], [pm_shuffle1])
    lines += [
        f"    have hRmsOut : {rms_post.fact_id}.Holds smFinal pmFinal := by",
        f"      change GeneratedPatterns.Ordinary2Rel (smStore {sm_rms.ins[0]}) (pmStore {pm_rms0.ins[0]}) (pmStore {pm_rms1.ins[0]}) {fs_rms} {ss_rms} at hRmsIn",
        f"      have core := GeneratedPatterns.Ordinary2Rel.rms_norm_2d hRmsIn hWeight (by decide : 0 < {shard_rms}) (by decide : 0 < {hidden_rms})",
        f"      change GeneratedPatterns.Ordinary2Rel (smFinal {sm_rms.outs[0]}) (pmFinal {pm_rms0.outs[0]}) (pmFinal {pm_rms1.outs[0]}) {fs_rms} {ss_rms}",
        "      rw [hSmRms, hPmRms0, hPmRms1]", "      exact core",
    ]

    def shuffle_writer(name, graph, store, final, node, before_nodes, after_nodes, buddies):
        data0, data1 = sm_shuffle.ins[0], sm_shuffle.ins[0]
        if node is not sm_shuffle:
            data0, data1 = pm_shuffle0.ins[0], pm_shuffle1.ins[0]
        rank = node.params[1]
        prefix = f"[{', '.join(_node_text(x) for x in before_nodes)}]"
        expr = f"ZigzagCollective.fw_maybe_shuffle_collective [{prefix}.foldl (applyNodeDistributedFaithful {graph}) {store} {data0}, {prefix}.foldl (applyNodeDistributedFaithful {graph}) {store} {data1}] (decodeCuSeqlens ({prefix}.foldl (applyNodeDistributedFaithful {graph}) {store} {metadata_tid})) {node.params[0]} {rank}"
        out = [
            f"    have {name}Writer : {final} {node.outs[0]} = {expr} := by",
            f"      simpa [{final}, {'smNodes' if final == 'smFinal' else 'pmNodes'}] using",
            f"        (foldl_faithful_middle_writer {graph} {store} {prefix} [{', '.join(_node_text(x) for x in after_nodes)}] {_node_text(node)} {node.outs[0]}",
            f"          (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t {data0}, t {data1}] (decodeCuSeqlens (t {metadata_tid})) {node.params[0]} {rank}) (by",
            "            intro t", "            rw [applyNodeDistributedFaithful_shuffle_out]",
            "            unfold applyNodeFaithfulShuffleValue",
            f"            rw [show {graph}.replicaBuddies {_node_text(node)} = [{', '.join(_node_text(x) for x in buddies)}] by native_decide]",
            "            rfl) (by native_decide) (by native_decide))",
            f"    have {name} : {final} {node.outs[0]} = applyNodeFaithfulShuffleValue {graph} {store} {_node_text(node)} := by",
            f"      rw [{name}Writer]",
            f"      change {expr} = _",
        ]
        for tid in dict.fromkeys((data0, data1, metadata_tid)):
            out += [
                f"      rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix} {store} {tid} (by native_decide) (by native_decide)]"
            ]
        out += [
            "      unfold applyNodeFaithfulShuffleValue",
            f"      rw [show {graph}.replicaBuddies {_node_text(node)} = [{', '.join(_node_text(x) for x in buddies)}] by native_decide]",
            "      rfl",
        ]
        return out

    lines += shuffle_writer("hSmShuffle", sm_graph, "smStore", "smFinal", sm_shuffle, [sm_rms], [], [sm_shuffle])
    lines += shuffle_writer("hPmShuffle0", pm_graph, "pmStore", "pmFinal", pm_shuffle0, [pm_rms0], pms[2:], [pm_shuffle0, pm_shuffle1])
    lines += shuffle_writer("hPmShuffle1", pm_graph, "pmStore", "pmFinal", pm_shuffle1, pms[:3], [], [pm_shuffle0, pm_shuffle1])
    lines += [
        f"    have hMetadataFinal : pmFinal {metadata_tid} = pmStore {metadata_tid} :=",
        f"      foldl_applyNodeDistributedFaithful_at_not_written {pm_graph} pmNodes pmStore {metadata_tid} (by native_decide) (by native_decide)",
        f"    have hShuffleOut : {shuffle_post.fact_id}.Holds smFinal pmFinal := by",
        f"      change GeneratedPatterns.Ordinary2Rel (smStore {sm_shuffle.ins[0]}) (pmStore {pm_shuffle0.ins[0]}) (pmStore {pm_shuffle1.ins[0]}) {fs_shuf} {ss_shuf} at hShuffleIn",
        "      have core := TrainVerify.Denote.RelationCompiler.Ordinary2Rel.to_zigzag_shuffle",
        f"        {sm_graph} {pm_graph} smStore pmStore {_node_text(sm_shuffle)} {_node_text(pm_shuffle0)} {_node_text(pm_shuffle1)} (pmStore {metadata_tid})",
        "        hShuffleIn hPackedActual (by native_decide) (by native_decide) (by native_decide)",
        "        rfl rfl rfl rfl rfl (by native_decide) rfl rfl rfl",
        f"      change GeneratedPatterns.Zigzag2Rel (smFinal {sm_shuffle.outs[0]}) (pmFinal {pm_shuffle0.outs[0]}) (pmFinal {pm_shuffle1.outs[0]}) (pmFinal {metadata_tid}) {fs_shuf} {ss_shuf}",
        "      rw [hSmShuffle, hPmShuffle0, hPmShuffle1, hMetadataFinal]",
        "      exact core",
        "    intro fact hfact",
        f"    have covered : fact ∈ [{rms_post.fact_id}, {shuffle_post.fact_id}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{rms_post.fact_id}, {shuffle_post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | hold",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with rfl | rfl",
        "      · exact hRmsOut", "      · exact hShuffleOut",
        "    · exact hframe fact hold", "",
    ]
    return "\n".join(lines)


def render_closed_segment(ir: GoalIR, relation, segment_id: str) -> str:
    """Render one closed segment through an explicit registered family adapter."""
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("closed segment dispatch requires a complete closed chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None:
        raise ValueError(f"unknown closed segment: {segment_id}")
    transitions = {item.transition_id: item for item in relation.transition_specs}
    family = tuple(transitions[item].rule_id for item in segment.transition_ids)

    if family and all(item == "multiref-projection-alias" for item in family):
        return render_closed_multiref_segment(ir, relation, segment_id)
    if (
        family
        and family[0] == "hidden-sharded-embedding-alltoall-ordinary-two-rank"
        and all(item == "init-lineage-full-to-two-chunks" for item in family[1:])
    ):
        return render_closed_initial_component(ir, relation, segment_id)
    if family == ("float-ordinary-two-rank",):
        return render_closed_float_segment(ir, relation, segment_id)
    if family in (("rms-norm-ordinary-two-rank",), ("rms-norm-zigzag-two-rank",)):
        return render_closed_rms_norm_segment(ir, relation, segment_id)
    if family == (
        "rms-norm-ordinary-two-rank",
        "faithful-maybe-shuffle-ordinary-to-zigzag-two-rank",
    ):
        return render_closed_rms_shuffle_segment(ir, relation, segment_id)
    if family in (
        ("elementwise-add-ordinary-two-rank",),
        ("elementwise-add-zigzag-two-rank",),
        ("broadcast-mul-ordinary-two-rank",),
        ("broadcast-mul-zigzag-two-rank",),
    ):
        return render_closed_binary_segment(ir, relation, segment_id)
    if family == ("rotary-embedding-two-output-ordinary-two-rank",):
        return render_closed_rotary_segment(ir, relation, segment_id)
    if family in (("attention-ordinary-qkv-two-rank",),
                   ("attention-zigzag-qkv-two-rank",)):
        return render_closed_attention_segment(ir, relation, segment_id)
    if family in (
        ("float-zigzag-two-rank",),
        ("identity-view-ordinary-two-rank",),
        ("identity-view-zigzag-two-rank",),
        ("identity-reshape-ordinary-two-rank",),
        ("identity-reshape-zigzag-two-rank",),
        ("flatten-3d-ordinary-two-rank",),
        ("flatten-3d-zigzag-two-rank",),
    ):
        return render_closed_unary_segment(ir, relation, segment_id)
    if family in (
        ("mix-precision-linear-ordinary-two-rank",),
        ("mix-precision-linear-zigzag-two-rank",),
    ) or (
        len(family) == 3
        and family[0] == "FW_per_head_mix_precision_linear-full-producer-chunks-ordinary-two-rank"
        and family[1:] == ("per-head-linear-ordinary-two-rank",) * 2
    ) or family == (
        "per-head-linear-ordinary-two-rank",
        "per-head-linear-ordinary-two-rank",
        "rms-norm-zigzag-two-rank",
    ):
        return render_closed_linear_segment(ir, relation, segment_id)
    if (
        len(family) > 1
        and family[0] == "FW_per_head_mix_precision_linear-full-producer-chunks-zigzag-two-rank"
        and all(item == "to-ordinary-two-rank" for item in family[1:])
    ):
        return render_closed_full_producer_to_segment(ir, relation, segment_id)
    if (
        len(family) == 16
        and family[0] in (
            "FW_norm_linear-full-producer-chunks-ordinary-two-rank",
            "FW_norm_linear-full-producer-chunks-zigzag-two-rank",
        )
    ):
        return render_closed_mixed_moe_segment(ir, relation, segment_id)
    raise ValueError(f"unsupported closed segment family {family!r} at {segment_id}")


def compose_closed_dependent_chain(
    ir: GoalIR, relation, namespace: str
) -> str:
    """Render a complete closed chain or stop at its first unsupported family."""
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("closed chain composition requires a complete closed chain")
    if not namespace or not namespace.replace("_", "").isalnum():
        raise ValueError(f"invalid closed chain namespace: {namespace!r}")
    transitions = {item.transition_id: item for item in relation.transition_specs}
    rendered: list[tuple[object, str, bool]] = []
    for segment in chain.segments:
        family = tuple(transitions[item].rule_id for item in segment.transition_ids)
        try:
            source = render_closed_segment(ir, relation, segment.segment_id)
        except ValueError as exc:
            raise ValueError(
                f"closed chain stopped at {segment.segment_id} family {family!r}: {exc}"
            ) from exc
        escaped_segment_id = re.escape(segment.segment_id)
        parameterized = re.search(
            rf"private(?: noncomputable)? def {escaped_segment_id}\s+"
            r"\(smGraph pmGraph : GraphDecl\)\s*:",
            source,
        )
        concrete = re.search(
            rf"private(?: noncomputable)? def {escaped_segment_id}\s*:",
            source,
        )
        if bool(parameterized) == bool(concrete):
            raise ValueError(
                f"closed segment {segment.segment_id} must declare exactly one concrete "
                "or graph-parameterized certificate"
            )
        rendered.append((segment, source, bool(concrete)))

    if not re.fullmatch(
        r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*",
        ir.public_statement_module,
    ):
        raise ValueError(
            f"invalid closed chain graph module: {ir.public_statement_module!r}"
        )
    declarations = render_closed_relation_declarations(chain, namespace)
    relation_import = "import denote.RelationCompiler\n"
    if not declarations.startswith(
        "/- AUTO-GENERATED closed relation state universe. -/\n" + relation_import
    ):
        raise ValueError("closed relation declarations have an unexpected import boundary")
    declarations = declarations.replace(
        relation_import,
        relation_import + f"import {ir.public_statement_module}\n",
        1,
    )
    marker = f"\nend\nend TrainVerify.Denote.{namespace}\n"
    if not declarations.endswith(marker):
        raise ValueError("closed relation declarations have an unexpected namespace boundary")
    states = {item.state_id: item for item in chain.states}
    final_state = states[chain.segments[-1].post_state_id]
    lines = [declarations[: -len(marker)]]
    lines.extend(source for _, source, _ in rendered)
    suffix_name = f"{namespace}_suffix_{len(rendered):06d}"
    lines.extend([
        f"private noncomputable def {suffix_name} :",
        f"    ClosedDepCertificateChain {ir.sm_graph_ref} {ir.pm_graph_ref} {final_state.state_id} {final_state.state_id} :=",
        f"  .nil {final_state.state_id}",
        "",
    ])
    for index in range(len(rendered) - 1, -1, -1):
        segment, _, concrete_graphs = rendered[index]
        next_name = suffix_name
        suffix_name = f"{namespace}_suffix_{index:06d}"
        head = segment.segment_id if concrete_graphs else (
            f"{segment.segment_id} {ir.sm_graph_ref} {ir.pm_graph_ref}"
        )
        lines.extend([
            f"private noncomputable def {suffix_name} :",
            f"    ClosedDepCertificateChain {ir.sm_graph_ref} {ir.pm_graph_ref} {segment.pre_state_id} {final_state.state_id} :=",
            f"  .cons {head} {next_name}",
            "",
        ])
    first_state = states[chain.segments[0].pre_state_id]
    chain_name = f"{namespace}_chain"
    lines.extend([
        f"noncomputable def {chain_name} :",
        f"    ClosedDepCertificateChain {ir.sm_graph_ref} {ir.pm_graph_ref} {first_state.state_id} {final_state.state_id} :=",
        f"  {suffix_name}",
        "",
        f"theorem {chain_name}_sm_nodes : {chain_name}.smNodes = {ir.sm_graph_ref}.nodes := by",
        "  native_decide",
        "",
        f"theorem {chain_name}_pm_nodes : {chain_name}.pmNodes = {ir.pm_graph_ref}.nodes := by",
        "  native_decide",
        marker.lstrip("\n"),
    ])
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
