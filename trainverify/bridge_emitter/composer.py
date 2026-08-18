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
        "set_option maxHeartbeats 500000",
        "noncomputable section",
        "",
    ]
    for fact in chain.relation_facts:
        if fact.kind == "sharded":
            if fact.gather_dim is None or not fact.pm_tids:
                raise ValueError(f"K-rank sharded fact is not closed: {fact.fact_id}")
            pm_tids = "[" + ", ".join(str(tid) for tid in fact.pm_tids) + "]"
            constructor = (
                f".sharded {fact.sm_tid} {pm_tids} {fact.gather_dim} "
                f"{shape_text(fact.full_shape)} {shape_text(fact.shard_shape)}"
            )
        elif fact.kind == "ordinary":
            constructor = (
                f".ordinary {fact.sm_tid} {fact.pm_rank0_tid} {fact.pm_rank1_tid} "
                f"{shape_text(fact.full_shape)} {shape_text(fact.shard_shape)}"
            )
        elif fact.kind == "label_chunks":
            constructor = (
                f".labelChunks {fact.sm_tid} {fact.pm_rank0_tid} {fact.pm_rank1_tid} "
                f"0 {shape_text(fact.full_shape)} {shape_text(fact.shard_shape)}"
            )
        elif fact.kind == "zigzag":
            if fact.metadata_tid is None:
                raise ValueError(f"zigzag fact lacks metadata: {fact.fact_id}")
            constructor = (
                f".zigzag {fact.sm_tid} {fact.pm_rank0_tid} {fact.pm_rank1_tid} "
                f"{fact.metadata_tid} {shape_text(fact.full_shape)} "
                f"{shape_text(fact.shard_shape)}"
            )
        elif fact.kind == "joined_ordinary":
            if fact.joined_pm_tid is None:
                raise ValueError(f"joined ordinary fact is not closed: {fact.fact_id}")
            constructor = (
                f".joinedOrdinary {fact.sm_tid} {fact.pm_rank0_tid} {fact.pm_rank1_tid} "
                f"{fact.joined_pm_tid} {shape_text(fact.full_shape)} "
                f"{shape_text(fact.shard_shape)}"
            )
        elif fact.kind == "joined_indexed_stack_dim1":
            if fact.gather_dim != 1 or not fact.source_tid_triples or fact.joined_pm_tid is None:
                raise ValueError(f"indexed-stack fact is not closed: {fact.fact_id}")
            sources = "[" + ", ".join(
                f"({sm_tid}, {pm0_tid}, {pm1_tid})"
                for sm_tid, pm0_tid, pm1_tid in fact.source_tid_triples
            ) + "]"
            constructor = (
                f".joinedIndexedStack {fact.sm_tid} {fact.pm_rank0_tid} {fact.pm_rank1_tid} "
                f"{fact.joined_pm_tid} {sources} {fact.gather_dim} "
                f"{shape_text(fact.full_shape)} {shape_text(fact.shard_shape)}"
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
        elif fact.kind == "label_bound":
            constructor = (
                f".labelBound .{fact.side} {fact.tid} "
                f"{fact.length} {fact.upper_bound}"
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
    """Extract one target value from one shared, named authority fold.

    Prefix and suffix stores are expressed with ``take``/``drop`` of the named
    node list.  This avoids repeating the full literal slice in every writer
    obligation while preserving the original authority order exactly.
    """
    target = nodes[position]
    if output_tid not in target.outs:
        raise ValueError(f"mixed target {name} does not write {output_tid}")
    prefix_nodes = f"({nodes_name}.take {position})"
    suffix_nodes = f"({nodes_name}.drop {position + 1})"
    prefix = (
        f"({prefix_nodes}).foldl "
        f"(applyNodeDistributedFaithful {graph}) {initial_store}"
    )
    expression_prefix = expression.format(store=prefix)
    expression_hybrid = expression.format(store=final_store)
    expression_at_t = expression.format(store="t")
    semantic_inputs = tuple(dict.fromkeys(input_tids))
    split_name = f"{name}_nodes"
    lines = [
        f"    have {split_name} : {nodes_name} = {prefix_nodes} ++ [{_node_text(target)}] ++ {suffix_nodes} := by",
        "      native_decide",
        f"    have {name}_prefix : {final_store} {output_tid} = {expression_prefix} := by",
        f"      rw [{final_equality}, {split_name}]",
        f"      exact foldl_faithful_middle_writer {graph} {initial_store}",
        f"        {prefix_nodes} {suffix_nodes}",
        f"        {_node_text(target)} {output_tid}",
        f"        (fun t => {expression_at_t}) (by",
        "          intro t",
    ]
    lines.extend(f"          {line}" for line in apply_lines)
    lines.append("        ) (by native_decide) (by native_decide)")
    read_names = []
    for ordinal, tid in enumerate(semantic_inputs):
        read_name = f"{name}_read_{ordinal}"
        read_names.append(read_name)
        lines.extend([
            f"    have {read_name} : {prefix} {tid} = {final_store} {tid} := by",
            f"      rw [{final_equality}, {split_name}]",
            f"      exact foldl_faithful_prefix_read_eq_final {graph} {initial_store}",
            f"        {prefix_nodes} ({_node_text(target)} :: {suffix_nodes}) {tid}",
            "        (by native_decide) (by native_decide)",
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
    if segment is None:
        raise ValueError("mixed MoE renderer requires one atomic component")
    by_id = {x.transition_id: x for x in relation.transition_specs}
    component_transitions = [by_id[x] for x in segment.transition_ids]
    projection_transitions = [
        transition for transition in component_transitions
        if transition.rule_id == "ordinary-topk-projection-two-rank"
    ]
    if len(projection_transitions) > 1:
        raise ValueError("mixed MoE renderer received multiple top-k projections")
    projection_transition = projection_transitions[0] if projection_transitions else None
    unshuffle_transitions = [
        transition for transition in component_transitions
        if transition.rule_id == "zigzag-topk-unshuffle-two-rank"
    ]
    if len(unshuffle_transitions) > 1:
        raise ValueError("mixed MoE renderer received multiple top-k unshuffles")
    unshuffle_transition = unshuffle_transitions[0] if unshuffle_transitions else None
    transitions = [
        transition for transition in component_transitions
        if transition.rule_id not in (
            "ordinary-topk-projection-two-rank",
            "zigzag-topk-unshuffle-two-rank",
        )
    ]
    if len(transitions) != 16:
        raise ValueError("mixed MoE renderer requires one 16-transition semantic core")
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
    elif rules == zigzag_rules and projection_transition is None:
        layout = "zigzag"
        relation_ns = "GeneratedPatterns.Zigzag2Rel"
    else:
        raise ValueError("mixed MoE renderer received a malformed ordinary/zigzag component")
    records = {x.source: x for x in chain.relation_facts}
    states = {x.state_id: x for x in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if projection_transition is not None:
        routing = transitions[7]
        route_sm = ir.sm_nodes[routing.sm_node_indices[0]]
        route_pm0 = ir.pm_nodes[routing.pm_node_indices[0]]
        route_pm1 = ir.pm_nodes[routing.pm_node_indices[1]]
        projection_post = records[projection_transition.post_facts[0]]
        if (
            projection_transition.pre_facts != routing.pre_facts
            or projection_transition.sm_node_indices != routing.sm_node_indices
            or projection_transition.pm_node_indices != routing.pm_node_indices
            or len(projection_transition.post_facts) != 1
            or projection_transition.lean_theorem
                != "TrainVerify.Denote.RelationCompiler.topk_routing_gate_scores_allGather0_commute_two"
            or (projection_post.sm_tid, projection_post.pm_rank0_tid, projection_post.pm_rank1_tid)
                != (route_sm.outs[2], route_pm0.outs[2], route_pm1.outs[2])
        ):
            raise ValueError("mixed MoE top-k projection does not share the exact routing owner")
    sms = ir.sm_nodes[slice(*segment.sm_range)]
    pms = ir.pm_nodes[slice(*segment.pm_range)]
    ownership_transitions = [*transitions]
    if unshuffle_transition is not None:
        ownership_transitions.append(unshuffle_transition)
    sm_owners = [index for transition in ownership_transitions for index in transition.sm_node_indices]
    pm_owners = [index for transition in ownership_transitions for index in transition.pm_node_indices]
    if (
        len(sm_owners) != len(set(sm_owners))
        or len(pm_owners) != len(set(pm_owners))
        or not sm_owners
        or not pm_owners
        or min(sm_owners) != segment.sm_range[0]
        or max(sm_owners) != segment.sm_range[1] - 1
        or min(pm_owners) != segment.pm_range[0]
        or max(pm_owners) != segment.pm_range[1] - 1
    ):
        raise ValueError("mixed MoE transition ownership does not span the exact ordered slice")
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
        if node.op == "FW_maybe_unshuffle":
            if (
                unshuffle_transition is None
                or out != node.outs[0]
                or len(ins) != 2
                or len(node.params or []) != 2
            ):
                raise ValueError("malformed mixed top-k unshuffle writer")
            if graph == ir.sm_graph_ref:
                peers = [node]
            elif graph == ir.pm_graph_ref:
                peers = [
                    ir.pm_nodes[index]
                    for index in unshuffle_transition.pm_node_indices
                ]
                peers.sort(key=lambda candidate: candidate.rank)
            else:
                raise ValueError("mixed unshuffle writer uses unknown graph")
            if (
                [peer.rank for peer in peers] != list(range(len(peers)))
                or any(peer.op != node.op or peer.ins[1] != ins[1] for peer in peers)
            ):
                raise ValueError("mixed unshuffle writer lacks exact rank-ordered peers")
            values = ", ".join(f"{{store}} {peer.ins[0]}" for peer in peers)
            expr = (
                f"ZigzagCollective.fw_maybe_unshuffle_collective [{values}] "
                f"(decodeCuSeqlens ({{store}} {ins[1]})) {node.params[0]} {node.params[1]}"
            )
            apply = [
                "rw [applyNodeDistributedFaithful_unshuffle_out]",
                "unfold applyNodeFaithfulUnshuffleValue",
                (
                    f"rw [show {graph}.replicaBuddies {_node_text(node)} = "
                    f"[{', '.join(_node_text(peer) for peer in peers)}] by native_decide]"
                ),
                "rfl",
            ]
            return expr, apply
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
        if node.op == "FW_maybe_unshuffle" and side == "pm":
            if unshuffle_transition is None:
                raise ValueError("mixed unshuffle writer has no transition owner")
            peers = [ir.pm_nodes[index] for index in unshuffle_transition.pm_node_indices]
            peers.sort(key=lambda candidate: candidate.rank)
            semantic_inputs.extend(peer.ins[0] for peer in peers)
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
        membership = [i for i, transition in enumerate(ownership_transitions)
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

    unshuffle_details = None
    if unshuffle_transition is not None:
        if layout != "zigzag":
            raise ValueError("mixed top-k unshuffle requires a zigzag semantic core")
        if (
            unshuffle_transition.lean_theorem
            != "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.unshuffle_gather_single"
            or len(unshuffle_transition.pre_facts) != 1
            or len(unshuffle_transition.post_facts) != 1
        ):
            raise ValueError("mixed top-k unshuffle certificate mismatch")
        unshuffle_pre = records[unshuffle_transition.pre_facts[0]]
        unshuffle_post = records[unshuffle_transition.post_facts[0]]
        routing = transitions[7]
        if unshuffle_transition.pre_facts != routing.pre_facts:
            raise ValueError("mixed top-k unshuffle does not share the routing input")
        usm = ir.sm_nodes[unshuffle_transition.sm_node_indices[0]]
        up0 = ir.pm_nodes[unshuffle_transition.pm_node_indices[0]]
        up1 = ir.pm_nodes[unshuffle_transition.pm_node_indices[1]]
        unodes = (usm, up0, up1)
        if (
            tuple(node.rank for node in unodes) != (0, 0, 1)
            or any(
                node.op != "FW_maybe_unshuffle"
                or len(node.ins) != 2
                or len(node.outs) != 1
                for node in unodes
            )
            or tuple(node.params for node in unodes) != ([1, 0], [2, 0], [2, 1])
        ):
            raise ValueError("mixed top-k unshuffle node roles mismatch")
        actual_metadata_tids = {node.ins[1] for node in unodes}
        if len(actual_metadata_tids) != 1:
            raise ValueError("mixed top-k unshuffle metadata bindings disagree")
        actual_metadata_tid = actual_metadata_tids.pop()
        route_sm = ir.sm_nodes[routing.sm_node_indices[0]]
        route_pm0 = ir.pm_nodes[routing.pm_node_indices[0]]
        route_pm1 = ir.pm_nodes[routing.pm_node_indices[1]]
        projections = []
        for route_node, unode in zip((route_sm, route_pm0, route_pm1), unodes):
            if unode.ins[0] not in route_node.outs:
                raise ValueError("mixed top-k unshuffle input lacks exact routing owner")
            projections.append(route_node.outs.index(unode.ins[0]))
        if len(set(projections)) != 1 or projections[0] not in (0, 1, 2):
            raise ValueError("mixed top-k unshuffle projection roles disagree")
        projection = projections[0]
        if (
            unshuffle_pre.kind != "zigzag"
            or unshuffle_post.kind != "ordinary"
            or unshuffle_post.metadata_tid is not None
            or unshuffle_pre.metadata_tid != metadata_tid
            or unshuffle_pre.full_shape != unshuffle_post.full_shape
            or unshuffle_pre.shard_shape != unshuffle_post.shard_shape
            or (unshuffle_post.sm_tid, unshuffle_post.pm_rank0_tid, unshuffle_post.pm_rank1_tid)
            != (usm.outs[0], up0.outs[0], up1.outs[0])
        ):
            raise ValueError("mixed top-k unshuffle relation payload mismatch")
        unshuffle_alias = authority_one(
            "tensor_eq",
            lambda fact: (
                fact.left_side, fact.left_tid, fact.right_side, fact.right_tid
            ) == (
                "pm", actual_metadata_tid, "pm", metadata_eq.right_tid
            ),
            f"top-k unshuffle metadata equality {actual_metadata_tid}",
        )
        lines.extend([
            f"    have hUnshuffleMetadataEq : pmFinal {actual_metadata_tid} = pmFinal {metadata_eq.right_tid} := by",
            f"      simpa [{unshuffle_alias.fact_id}, RelationFact.Holds, StoreSide.read] using (hframe _ (by native_decide : {unshuffle_alias.fact_id} ∈ {before.state_id}.facts))",
            f"    have hSharedMetadata : pmFinal {metadata_tid} = pmFinal {actual_metadata_tid} :=",
            "      hMetadataEq.trans hUnshuffleMetadataEq.symm",
            f"    have hUnshuffleDecoded : decodeCuSeqlens (pmFinal {actual_metadata_tid}) = [0, {packed_cu.total_tokens}] := by",
            "      rw [hUnshuffleMetadataEq]",
            "      exact hPackedCu.decoded_single",
        ])
        unshuffle_details = (
            unshuffle_pre, unshuffle_post, usm, up0, up1, projection,
            actual_metadata_tid,
        )

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
            if projection_transition is not None:
                projection_post = records[projection_transition.post_facts[0]]
                score_names = []
                for label, node, side, idx in (
                    ("Sm", sm, "sm", routing.sm_node_indices[0]),
                    ("P0", p0, "pm", routing.pm_node_indices[0]),
                    ("P1", p1, "pm", routing.pm_node_indices[1]),
                ):
                    src = writer_with_initial_inputs(
                        ensure_value(side, idx, node.outs[2]), side, node
                    )
                    name = f"hRoute{label}2"
                    shape_field = (
                        "full_shape" if side == "sm"
                        else ("rank0_shape" if label == "P0" else "rank1_shape")
                    )
                    lines += [
                        f"    have {name} := {src}",
                        f"    rw [{hin}.{shape_field}] at {name}",
                        f"    simp at {name}",
                    ]
                    score_names.append(name)
                lines += [
                    (
                        f"    have hRouteScoresCore := Ordinary2Rel.topk_routing_gate_scores "
                        f"{pres[0].shard_shape[0]} {pres[0].shard_shape[1]} {sm.params[0]} "
                        f"{hin} (by decide) (by decide)"
                    ),
                    f"    have hFactProjection : {projection_post.fact_id}.Holds smFinal pmFinal := by",
                    f"      change {rel_text(projection_post)}",
                    f"      rw [{', '.join(score_names)}]",
                    "      exact hRouteScoresCore",
                ]
                proved[projection_post.fact_id] = "hFactProjection"
            if unshuffle_details is not None:
                (
                    unshuffle_pre, unshuffle_post, usm, up0, up1, projection,
                    actual_metadata_tid,
                ) = unshuffle_details
                selected_names = []
                for label, node, side, idx in (
                    ("Sm", sm, "sm", routing.sm_node_indices[0]),
                    ("P0", p0, "pm", routing.pm_node_indices[0]),
                    ("P1", p1, "pm", routing.pm_node_indices[1]),
                ):
                    source = writer_with_initial_inputs(
                        ensure_value(side, idx, node.outs[projection]), side, node
                    )
                    name = f"hUnshuffleRoute{label}"
                    shape_field = (
                        "full_shape" if side == "sm"
                        else ("rank0_shape" if label == "P0" else "rank1_shape")
                    )
                    lines += [
                        f"    have {name} := {source}",
                        f"    rw [{hin}.{shape_field}] at {name}",
                        f"    simp at {name}",
                    ]
                    selected_names.append(name)
                core_projection = ("hRouteCore.1", "hRouteCore.2.1", "hRouteCore.2.2")[projection]
                husm = writer_with_initial_inputs(
                    ensure_value("sm", unshuffle_transition.sm_node_indices[0], usm.outs[0]),
                    "sm", usm,
                )
                hup0 = writer_with_initial_inputs(
                    ensure_value("pm", unshuffle_transition.pm_node_indices[0], up0.outs[0]),
                    "pm", up0,
                )
                hup1 = writer_with_initial_inputs(
                    ensure_value("pm", unshuffle_transition.pm_node_indices[1], up1.outs[0]),
                    "pm", up1,
                )
                shard_rows = unshuffle_post.shard_shape[0]
                tail = list(unshuffle_post.shard_shape[1:])
                fs = _shape_text(list(unshuffle_post.full_shape))
                ss = _shape_text(list(unshuffle_post.shard_shape))
                lines += [
                    f"    have hUnshuffleInput : GeneratedPatterns.Zigzag2Rel (smFinal {usm.ins[0]}) (pmFinal {up0.ins[0]}) (pmFinal {up1.ins[0]}) (pmFinal {metadata_tid}) {fs} {ss} := by",
                    f"      rw [{', '.join(selected_names)}]",
                    f"      exact {core_projection}",
                    "    rw [hSharedMetadata] at hUnshuffleInput",
                    f"    have hUnshuffleCore : smFinal {usm.ins[0]} = allGatherPrimDimN 0 2 0",
                    f"        [ZigzagCollective.fw_maybe_unshuffle_collective [pmFinal {up0.ins[0]}, pmFinal {up1.ins[0]}] (decodeCuSeqlens (pmFinal {actual_metadata_tid})) 2 0,",
                    f"         ZigzagCollective.fw_maybe_unshuffle_collective [pmFinal {up0.ins[0]}, pmFinal {up1.ins[0]}] (decodeCuSeqlens (pmFinal {actual_metadata_tid})) 2 1] := by",
                    f"      exact GeneratedPatterns.Zigzag2Rel.unshuffle_gather_single {shard_rows} {_shape_text(tail)} hUnshuffleInput",
                    "        (by decide) (by decide) rfl hUnshuffleDecoded",
                    f"    have hFactUnshuffle : {unshuffle_post.fact_id}.Holds smFinal pmFinal := by",
                    f"      change GeneratedPatterns.Ordinary2Rel (smFinal {usm.outs[0]}) (pmFinal {up0.outs[0]}) (pmFinal {up1.outs[0]}) {fs} {ss}",
                    "      refine {",
                    "        full_value := ?_",
                    "        full_shape := ?_",
                    "        rank0_shape := ?_",
                    "        rank1_shape := ?_",
                    "      }",
                    f"      · rw [{husm}, {hup0}, {hup1}]",
                    "        simp only [ZigzagCollective.fw_maybe_unshuffle_collective_cpSize_one, List.getD_cons_zero]",
                    "        exact hUnshuffleCore",
                    f"      · rw [{husm}]",
                    "        simp only [ZigzagCollective.fw_maybe_unshuffle_collective_cpSize_one, List.getD_cons_zero]",
                    "        exact hUnshuffleInput.full_shape",
                    f"      · rw [{hup0}, ZigzagCollective.fw_maybe_unshuffle_collective_shape]",
                    "        simp only [List.getD_cons_zero]",
                    "        exact hUnshuffleInput.rank0_shape",
                    f"      · rw [{hup1}, ZigzagCollective.fw_maybe_unshuffle_collective_shape]",
                    "        simp only [List.getD_cons_succ, List.getD_cons_zero]",
                    "        exact hUnshuffleInput.rank1_shape",
                ]
                proved[unshuffle_post.fact_id] = "hFactUnshuffle"
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
    missing_fresh = [fact.fact_id for fact in fresh if fact.fact_id not in proved]
    if missing_fresh:
        raise ValueError(f"mixed MoE lacks proofs for fresh post facts: {missing_fresh}")
    fresh_cases = " | ".join("rfl" for _ in fresh)
    fresh_proofs = [f"      · exact {proved[fact.fact_id]}" for fact in fresh]
    lines += [
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(x.fact_id for x in fresh)}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(x.fact_id for x in fresh)}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        f"      rcases fresh with {fresh_cases}",
        *fresh_proofs,
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
    prefix_name = f"{segment.segment_id}_sound_prefix"
    prefix_semantic_source = "\n".join(lines[semantic_start:semantic_split])
    record_by_id = {fact.fact_id: fact for fact in chain.relation_facts}
    prefix_outputs = [
        (record_by_id[fact_id], proof_name)
        for fact_id, proof_name in proved.items()
        if f"have {proof_name} :" in prefix_semantic_source
    ]
    if not prefix_outputs:
        raise ValueError("mixed MoE semantic prefix proves no relation facts")
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
    if unshuffle_transition is not None:
        prefix_lines.extend([
            f"    (hSharedMetadata : pmFinal {metadata_tid} = pmFinal {actual_metadata_tid})",
            f"    (hUnshuffleDecoded : decodeCuSeqlens (pmFinal {actual_metadata_tid}) = [0, {packed_cu.total_tokens}])",
        ])
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
        (" hDecodedCu" if layout == "zigzag" else "") +
        (" hSharedMetadata hUnshuffleDecoded" if unshuffle_transition is not None else ""),
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

    sm_graph, pm_graph = ir.sm_graph_ref, ir.pm_graph_ref
    lines = [
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {sm_graph} {pm_graph} {before.state_id} {after.state_id} where",
        f"  smNodes := [{sm_text}]",
        f"  pmNodes := [{', '.join(pm_text)}]",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := [{sm_text}]",
        f"    let pmNodes : List NodeDecl := [{', '.join(pm_text)}]",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {sm_graph}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hpos : {positions.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hq : {q_rel.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hk : {k_rel.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hcache : {cache_fact.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
    ]
    for prefix, graph, store, nodes, pos, node, final in (
        ("sm", sm_graph, "smStore", sm_nodes, 0, sm, "smFinal"),
        ("p0", pm_graph, "pmStore", pm_nodes, 0, p0, "pmFinal"),
        ("p1", pm_graph, "pmStore", pm_nodes, 1, p1, "pmFinal"),
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
    """Render one atomic zigzag full producer with optional ordinary FW_to fanout."""
    try:
        from .relation_compiler import (
            FrontierToCertificate,
            FullProducerChunkCertificate,
        )
    except ImportError:
        from relation_compiler import (
            FrontierToCertificate,
            FullProducerChunkCertificate,
        )

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
    if len(full_transitions) != 1 or len(transitions) != 1 + len(to_transitions):
        raise ValueError("component is not one zigzag full producer with optional ordinary FW_to transitions")
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
    try:
        from .relation_compiler import (
            FrontierLinearCertificate,
            FrontierRMSNormCertificate,
            FullProducerChunkCertificate,
            PerHeadLinearRelationCertificate,
        )
    except ImportError:
        from relation_compiler import (
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
        transition_parts = transition.transition_id.split(":", 2)
        if len(transition_parts) != 3 or transition_parts[2] != transition.rule_id:
            raise ValueError("linear transition has malformed certificate identity")
        certificate_class = transition_parts[1]
        cert_matches = [
            c for c in certs
            if type(c).__name__ == certificate_class
            and getattr(c, "rule_id", None) == transition.rule_id
            and getattr(c, "output_step_triple", None) == post.source.step_triple
        ]
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
        posts = [records[source] for source in t.post_facts]
        ordinary = [item for item in posts if item.kind == "ordinary"]
        label_chunks = [item for item in posts if item.kind == "label_chunks"]
        if len(ordinary) != 1 or len(label_chunks) != 1:
            raise ValueError("InitChunk transition lacks ordinary/label-chunk facts")
        post, label_post = ordinary[0], label_chunks[0]
        p0i,p1i=t.pm_node_indices;p0,p1=ir.pm_nodes[p0i],ir.pm_nodes[p1i];full=int(post.source.step_triple[0].split(':')[1]);eq=eq_fact("sm",full,"pm",p0.ins[0]);shape=shape_fact("pm",p0.ins[0])
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
          f"      exact TrainVerify.Denote.RelationCompiler.Ordinary2Rel.of_eq_chunk2_dim0_1d _ _ {post.shard_shape[0]} hEq{k} (by simpa using hShape{k}) (by decide)",
          f"    have hout_label_chunks{k} : {label_post.fact_id}.Holds smFinal pmFinal := by",
          f"      change pmFinal {label_post.pm_rank0_tid} = chunkPrimDimN 0 2 0 (pmFinal {label_post.sm_tid}) ∧ _",
          f"      have hFullFinal{k} : pmFinal {label_post.sm_tid} = pmStore {label_post.sm_tid} := foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore {label_post.sm_tid} (by native_decide) (by native_decide)",
          f"      rw [hChunk{k}_0, hChunk{k}_1, hFullFinal{k}]",
          f"      exact ⟨rfl, rfl, hShape{k}, hout_init{k}.rank0_shape, hout_init{k}.rank1_shape⟩"]
        fresh.extend((post, label_post))
    if not set(after.fact_ids)<=({x.fact_id for x in fresh}|set(before.fact_ids)): raise ValueError("initial component introduces unproved fact")
    names=["hout_embedding"]+[name for k in range(len(init))
        for name in (f"hout_init{k}", f"hout_label_chunks{k}")];defs=[x.fact_id for x in fresh]
    lines += ["    intro fact hfact",f"    have covered : fact ∈ [{', '.join(defs)}] ++ {before.state_id}.facts := by",f"      exact (show {after.state_id}.facts ⊆ [{', '.join(defs)}] ++ {before.state_id}.facts by native_decide) hfact","    simp only [List.mem_append] at covered","    rcases covered with fresh | hold","    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with "+" | ".join(["rfl"]*len(names))]
    lines += [f"      · exact {x}" for x in names]+["    · exact hframe fact hold",""]
    return "\n".join(lines)



def render_closed_ce_snd_segment(ir: GoalIR, relation, segment_id: str) -> str:
    """Render a two-rank InnerChunk CE z-loss terminal without label authority."""
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("CE .snd renderer requires a complete closed chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("CE .snd segment must own one transition")
    transition = {item.transition_id: item for item in relation.transition_specs}[
        segment.transition_ids[0]
    ]
    expected_theorem = "TrainVerify.Denote.fw_inner_chunk_ce_snd_allGatherDim0_shards"
    if transition.rule_id != "inner-chunk-ce-projection-gather-two-rank":
        raise ValueError("segment is not the registered CE terminal family")
    if transition.lean_theorem != expected_theorem:
        raise ValueError(f"CE .snd renderer theorem mismatch: {transition.lean_theorem}")
    if len(transition.pre_facts) != 1 or len(transition.post_facts) != 1:
        raise ValueError("CE .snd transition must have one pre/post fact")

    sms = ir.sm_nodes[slice(*segment.sm_range)]
    pms = ir.pm_nodes[slice(*segment.pm_range)]
    if len(sms) != 1 or len(pms) != 3:
        raise ValueError("CE .snd node roles require one SM CE and two PM CE plus gather")
    sm, p0, p1 = sms[0], pms[0], pms[1]
    gather = pms[2]
    ce_nodes = (sm, p0, p1)
    valid_ce = all(
        node.op == "FW_inner_chunk_ce"
        and len(node.ins) == 3
        and len(node.outs) == 2
        and len(node.params or ()) == 1
        for node in ce_nodes
    )
    if (
        not valid_ce
        or (sm.rank, p0.rank, p1.rank) != (0, 0, 1)
        or any(tuple(node.params or ()) != tuple(sm.params or ()) for node in (p0, p1))
        or gather.op != "AllGatherPrim"
        or gather.rank != 0
        or gather.params != [0]
        or gather.ins != [p0.outs[1], p1.outs[1]]
        or gather.outs != [sm.outs[1]]
    ):
        raise ValueError("CE .snd node roles do not match projection/gather")
    weight = sm.ins[1]
    if p0.ins[1] != weight or p1.ins[1] != weight:
        raise ValueError("CE .snd node roles require one shared weight")

    records = {item.source: item for item in chain.relation_facts}
    pre = records[transition.pre_facts[0]]
    post = records[transition.post_facts[0]]
    if (
        pre.kind != "ordinary"
        or post.kind != "joined_ordinary"
        or post.joined_pm_tid != gather.outs[0]
        or (pre.sm_tid, pre.pm_rank0_tid, pre.pm_rank1_tid)
        != (sm.ins[0], p0.ins[0], p1.ins[0])
        or (post.sm_tid, post.pm_rank0_tid, post.pm_rank1_tid)
        != (sm.outs[1], p0.outs[1], p1.outs[1])
        or len(pre.shard_shape) != 2
        or pre.full_shape != (pre.shard_shape[0] * 2, pre.shard_shape[1])
        or post.full_shape != (pre.full_shape[0],)
        or post.shard_shape != (pre.shard_shape[0],)
    ):
        raise ValueError("CE .snd relation payload does not match exact node roles")
    shard_rows, hidden = pre.shard_shape

    eq_facts = [
        item for item in chain.authority_facts
        if item.kind == "tensor_eq"
        and (item.left_side, item.left_tid, item.right_side, item.right_tid)
        == ("sm", weight, "pm", weight)
    ]
    shape_facts = [
        item for item in chain.authority_facts
        if item.kind == "tensor_shape" and (item.side, item.tid) == ("pm", weight)
    ]
    if len(eq_facts) != 1 or len(shape_facts) != 1:
        raise ValueError("CE .snd weight authority is missing or ambiguous")
    weight_eq, weight_shape = eq_facts[0], shape_facts[0]
    if len(weight_shape.shape) != 2 or weight_shape.shape[1] != hidden:
        raise ValueError("CE .snd weight shape authority disagrees with activation")
    vocab = weight_shape.shape[0]

    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {pre.fact_id, weight_eq.fact_id, weight_shape.fact_id}
    if not required <= set(before.fact_ids) or post.fact_id not in after.fact_ids:
        raise ValueError("CE .snd activation/weight authority is not live")
    if not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("CE .snd state introduces an unproved fact")

    sm_nodes = [_node_text(sm)]
    pm_nodes = [_node_text(item) for item in pms]
    sm_text = "[" + ", ".join(sm_nodes) + "]"
    pm_text = "[" + ", ".join(pm_nodes) + "]"
    params_text = _shape_text(sm.params or [])
    zscale = "(((0 : Nat) : Scalar))"
    fs, ss = _shape_text(post.full_shape), _shape_text(post.shard_shape)
    pre_fs, pre_ss = _shape_text(pre.full_shape), _shape_text(pre.shard_shape)
    weight_shape_text = _shape_text(weight_shape.shape)

    sm_graph, pm_graph = ir.sm_graph_ref, ir.pm_graph_ref
    sm_nodes_name = f"{segment.segment_id}_sm_nodes"
    pm_nodes_name = f"{segment.segment_id}_pm_nodes"
    sm_final_name = f"{segment.segment_id}_sm_final"
    pm_final_name = f"{segment.segment_id}_pm_final"

    def writer(helper_name, graph, store, final_name, nodes_name, nodes, position):
        node = nodes[position]
        before_nodes, after_nodes = nodes[:position], nodes[position + 1:]
        prefix_text = f"[{', '.join(_node_text(item) for item in before_nodes)}]"
        after_text = f"[{', '.join(_node_text(item) for item in after_nodes)}]"
        prefix = f"{prefix_text}.foldl (applyNodeDistributedFaithful {graph}) {store}"

        def expr(st):
            return (
                f"(fw_inner_chunk_ce ({st} {node.ins[0]}) ({st} {node.ins[1]}) "
                f"({st} {node.ins[2]}) (((({st} {node.ins[1]}).shape.head?).getD 0)) "
                f"{zscale}).snd"
            )

        lines = [
            f"private theorem {helper_name} ({store} : Store) :",
            f"    {final_name} {store} {node.outs[1]} = {expr(store)} := by",
        ]
        reads = []
        for ordinal, tid in enumerate(dict.fromkeys(node.ins)):
            read = f"hread_{ordinal}"
            reads.append(read)
            lines.extend([
                f"  have {read} : {prefix} {tid} = {store} {tid} := by",
                f"    exact foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix_text} {store} {tid}",
                "      (by native_decide) (by native_decide)",
            ])
        lines.extend([
            "  calc",
            f"    {final_name} {store} {node.outs[1]} = {expr(prefix)} := by",
            f"      unfold {final_name}",
            f"      rw [show {nodes_name} = {prefix_text} ++ [{_node_text(node)}] ++ {after_text} by native_decide]",
            f"      exact foldl_faithful_middle_writer {graph} {store} {prefix_text}",
            f"        {after_text} {_node_text(node)}",
            f"        {node.outs[1]} (fun t => {expr('t')}) (by",
            "          intro t",
            "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "            (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]",
            "          unfold applyNodeDistributed",
            "          rw [if_neg (by decide)]",
            "          rw [applyNodeRingAttn_eq_applyNode_of_not_ring]",
            (f"          · exact applyNode_fw_inner_chunk_ce_snd_out_1p {graph} t {node.rank} "
            f"{node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by decide) (params := {params_text})"),
            "          · decide",
            "          · decide",
            "        ) (by native_decide) (by native_decide)",
            f"    _ = {expr(store)} := by",
            f"      rw [{', '.join(reads)}]" if reads else "      rfl",
            "",
        ])
        return lines

    sm_writer_name = f"{segment.segment_id}_sm_writer_value"
    pm0_writer_name = f"{segment.segment_id}_pm0_writer_value"
    pm1_writer_name = f"{segment.segment_id}_pm1_writer_value"
    gather_writer_name = f"{segment.segment_id}_gather_writer_value"
    core_name = f"{segment.segment_id}_semantic_core"
    shapes_name = f"{segment.segment_id}_output_shapes"
    output_name = f"{segment.segment_id}_output_relation"

    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := {sm_text}",
        f"private def {pm_nodes_name} : List NodeDecl := {pm_text}",
        f"private def {sm_final_name} (smStore : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {sm_graph}) smStore",
        f"private def {pm_final_name} (pmStore : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore",
        "",
    ]
    lines += writer(sm_writer_name, sm_graph, "smStore", sm_final_name, sm_nodes_name, [sm], 0)
    lines += writer(pm0_writer_name, pm_graph, "pmStore", pm_final_name, pm_nodes_name, pms, 0)
    lines += writer(pm1_writer_name, pm_graph, "pmStore", pm_final_name, pm_nodes_name, pms, 1)
    gather_prefix = pms[:2]
    gather_prefix_text = "[" + ", ".join(_node_text(item) for item in gather_prefix) + "]"
    gather_text = _node_text(gather)
    lines += [
        f"private theorem {gather_writer_name} (pmStore : Store) :",
        f"    {pm_final_name} pmStore {gather.outs[0]} =",
        f"      allGatherPrimDimN 0 2 0 [{pm_final_name} pmStore {gather.ins[0]}, {pm_final_name} pmStore {gather.ins[1]}] := by",
        f"  have hWriter : {pm_final_name} pmStore {gather.outs[0]} =",
        f"      allGatherPrimDimN 0 2 0 [({gather_prefix_text}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[0]},",
        f"        ({gather_prefix_text}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[1]}] := by",
        f"    unfold {pm_final_name}",
        f"    rw [show {pm_nodes_name} = {gather_prefix_text} ++ [{gather_text}] ++ [] by native_decide]",
        f"    exact foldl_faithful_middle_writer {pm_graph} pmStore {gather_prefix_text} [] {gather_text} {gather.outs[0]}",
        f"      (fun t => allGatherPrimDimN 0 2 0 [t {gather.ins[0]}, t {gather.ins[1]}]) (by",
        "        intro t",
        "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "          (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]",
        "        unfold applyNodeDistributed",
        "        rw [if_neg (by decide)]",
        "        rw [applyNodeRingAttn_eq_applyNode_of_not_ring]",
        f"        · exact applyNode_allGatherPrimDimN_out {pm_graph} t {gather.rank} [{gather.ins[0]}, {gather.ins[1]}] {gather.outs[0]} 0",
        "        · decide", "        · decide",
        "      ) (by native_decide) (by native_decide)",
        f"  have h0 := foldl_faithful_prefix_read_eq_final {pm_graph} pmStore {gather_prefix_text} [{gather_text}] {gather.ins[0]} (by native_decide) (by native_decide)",
        f"  have h1 := foldl_faithful_prefix_read_eq_final {pm_graph} pmStore {gather_prefix_text} [{gather_text}] {gather.ins[1]} (by native_decide) (by native_decide)",
        f"  change ({gather_prefix_text}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[0]} = {pm_final_name} pmStore {gather.ins[0]} at h0",
        f"  change ({gather_prefix_text}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[1]} = {pm_final_name} pmStore {gather.ins[1]} at h1",
        "  rw [h0, h1] at hWriter", "  exact hWriter", "",
    ]
    lines += [
        f"private theorem {core_name} (smStore pmStore : Store)",
        f"    (hIn : GeneratedPatterns.Ordinary2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) {pre_fs} {pre_ss})",
        f"    (hWeightEq : smStore {weight} = pmStore {weight})",
        f"    (hWeightShape : (pmStore {weight}).shape = {weight_shape_text}) :",
        f"    (fw_inner_chunk_ce (smStore {sm.ins[0]}) (smStore {weight}) (smStore {sm.ins[2]}) {vocab} {zscale}).snd =",
        f"      allGatherPrimDimN 0 2 0 [(fw_inner_chunk_ce (pmStore {p0.ins[0]}) (pmStore {weight}) (pmStore {p0.ins[2]}) {vocab} {zscale}).snd,",
        f"        (fw_inner_chunk_ce (pmStore {p1.ins[0]}) (pmStore {weight}) (pmStore {p1.ins[2]}) {vocab} {zscale}).snd] := by",
        f"  have hPm0Labels : (fw_inner_chunk_ce (pmStore {p0.ins[0]}) (pmStore {weight}) (pmStore {p0.ins[2]}) {vocab} {zscale}).snd =",
        f"      (fw_inner_chunk_ce (pmStore {p0.ins[0]}) (pmStore {weight}) (smStore {sm.ins[2]}) {vocab} {zscale}).snd := by",
        "    exact RelationCompiler.inner_chunk_ce_snd_labels_independent _ _ _ _ _ _",
        f"  have hPm1Labels : (fw_inner_chunk_ce (pmStore {p1.ins[0]}) (pmStore {weight}) (pmStore {p1.ins[2]}) {vocab} {zscale}).snd =",
        f"      (fw_inner_chunk_ce (pmStore {p1.ins[0]}) (pmStore {weight}) (smStore {sm.ins[2]}) {vocab} {zscale}).snd := by",
        "    exact RelationCompiler.inner_chunk_ce_snd_labels_independent _ _ _ _ _ _",
        "  rw [hPm0Labels, hPm1Labels]",
        "  rw [hWeightEq, hIn.full_value]",
        f"  simpa using (fw_inner_chunk_ce_snd_allGatherDim0_shards 2 {shard_rows} {hidden} {vocab} {zscale}",
        f"    [pmStore {p0.ins[0]}, pmStore {p1.ins[0]}] (pmStore {weight}) (smStore {sm.ins[2]})",
        "    (by decide) (by decide) (by decide) (by decide)",
        "    (by exact hIn.rank0_shape)",
        "    (by",
        "      intro r hr",
        "      have hr' : r = 0 ∨ r = 1 := by omega",
        "      rcases hr' with rfl | rfl",
        "      · exact hIn.rank0_shape",
        "      · exact hIn.rank1_shape)",
        "    hWeightShape)",
        "",
        f"private theorem {shapes_name} (smStore pmStore : Store)",
        f"    (hIn : GeneratedPatterns.Ordinary2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) {pre_fs} {pre_ss}) :",
        f"    (fw_inner_chunk_ce (smStore {sm.ins[0]}) (smStore {weight}) (smStore {sm.ins[2]}) (((smStore {weight}).shape.head?).getD 0) {zscale}).snd.shape = {fs} ∧",
        f"    (fw_inner_chunk_ce (pmStore {p0.ins[0]}) (pmStore {weight}) (pmStore {p0.ins[2]}) (((pmStore {weight}).shape.head?).getD 0) {zscale}).snd.shape = {ss} ∧",
        f"    (fw_inner_chunk_ce (pmStore {p1.ins[0]}) (pmStore {weight}) (pmStore {p1.ins[2]}) (((pmStore {weight}).shape.head?).getD 0) {zscale}).snd.shape = {ss} := by",
        "  refine ⟨?_, ?_, ?_⟩",
        f"  · apply fw_inner_chunk_ce_snd_shape _ _ _ _ {zscale} {pre.full_shape[0]}",
        "    rw [hIn.full_shape]",
        "    rfl",
        f"  · apply fw_inner_chunk_ce_snd_shape _ _ _ _ {zscale} {shard_rows}",
        "    rw [hIn.rank0_shape]",
        "    rfl",
        f"  · apply fw_inner_chunk_ce_snd_shape _ _ _ _ {zscale} {shard_rows}",
        "    rw [hIn.rank1_shape]",
        "    rfl",
        "",
        f"private theorem {output_name} (smStore pmStore : Store)",
        f"    (hIn : GeneratedPatterns.Ordinary2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) {pre_fs} {pre_ss})",
        f"    (hWeightEq : smStore {weight} = pmStore {weight})",
        f"    (hWeightShape : (pmStore {weight}).shape = {weight_shape_text}) :",
        f"    {post.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  have hSmWriter := {sm_writer_name} smStore",
        f"  have hPm0Writer := {pm0_writer_name} pmStore",
        f"  have hPm1Writer := {pm1_writer_name} pmStore",
        f"  have hGatherWriter := {gather_writer_name} pmStore",
        f"  have hCore := {core_name} smStore pmStore hIn hWeightEq hWeightShape",
        f"  obtain ⟨hSmShape, hPm0Shape, hPm1Shape⟩ := {shapes_name} smStore pmStore hIn",
        f"  change JoinedOrdinary2Rel ({sm_final_name} smStore {sm.outs[1]}) ({pm_final_name} pmStore {p0.outs[1]}) ({pm_final_name} pmStore {p1.outs[1]}) ({pm_final_name} pmStore {gather.outs[0]}) {fs} {ss}",
        "  have hOrdinary : GeneratedPatterns.Ordinary2Rel",
        f"      ({sm_final_name} smStore {sm.outs[1]}) ({pm_final_name} pmStore {p0.outs[1]}) ({pm_final_name} pmStore {p1.outs[1]}) {fs} {ss} := by",
        "    refine {",
        "      full_value := ?_",
        "      full_shape := ?_",
        "      rank0_shape := ?_",
        "      rank1_shape := ?_",
        "    }",
        "    · rw [hSmWriter, hPm0Writer, hPm1Writer]",
        f"      rw [show (((smStore {weight}).shape.head?).getD 0) = {vocab} by rw [hWeightEq, hWeightShape]; rfl]",
        f"      rw [show (((pmStore {weight}).shape.head?).getD 0) = {vocab} by rw [hWeightShape]; rfl]",
        "      exact hCore",
        "    · rw [hSmWriter]",
        "      exact hSmShape",
        "    · rw [hPm0Writer]",
        "      exact hPm0Shape",
        "    · rw [hPm1Writer]",
        "      exact hPm1Shape",
        "  refine { toOrdinary2Rel := hOrdinary, joined_value := hGatherWriter, public_value := ?_ }",
        "  exact hOrdinary.full_value.trans hGatherWriter.symm",
        "",
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {sm_graph} {pm_graph} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}",
        f"  pmNodes := {pm_nodes_name}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smFinal := {sm_final_name} smStore",
        f"    let pmFinal := {pm_final_name} pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"      apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "      · native_decide",
        "      · native_decide",
        "      · native_decide",
        "      · native_decide",
        f"    have hIn : {pre.fact_id}.Holds smStore pmStore := hstate {pre.fact_id} (by native_decide)",
        f"    change GeneratedPatterns.Ordinary2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) {pre_fs} {pre_ss} at hIn",
        f"    have hWeightEq : {weight_eq.fact_id}.Holds smStore pmStore := hstate {weight_eq.fact_id} (by native_decide)",
        f"    change smStore {weight} = pmStore {weight} at hWeightEq",
        f"    have hWeightShape : {weight_shape.fact_id}.Holds smStore pmStore := hstate {weight_shape.fact_id} (by native_decide)",
        f"    change (pmStore {weight}).shape = {weight_shape_text} at hWeightShape",
        f"    have hOut := {output_name} smStore pmStore hIn hWeightEq hWeightShape",
        "    change " + f"{post.fact_id}.Holds smFinal pmFinal at hOut",
        "    change " + f"{after.state_id}.Holds smFinal pmFinal",
        "    exact RelationState.Holds.mono_insert hframe hOut (by native_decide)",
        "",
    ]
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



def render_closed_unshuffle_segment(ir: GoalIR, relation, segment_id: str) -> str:
    """Render a faithful two-rank zigzag exit as one exact fold per authority."""
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("exit-unshuffle segment requires a complete closed chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("exit-unshuffle segment must own one transition")
    transitions = {item.transition_id: item for item in relation.transition_specs}
    transition = transitions[segment.transition_ids[0]]
    if transition.rule_id != "zigzag-to-ordinary-unshuffle-two-rank" or transition.lean_theorem != (
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.to_gather2_unshuffle"
    ):
        raise ValueError("segment is not the registered exit-unshuffle family")
    if ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2:
        raise ValueError("exit-unshuffle requires exact SM=1/PM=2 graph ranks")
    if transition.sm_node_indices != tuple(range(*segment.sm_range)) or transition.pm_node_indices != tuple(
        range(*segment.pm_range)
    ):
        raise ValueError("exit-unshuffle transition/segment footprint mismatch")
    sms = ir.sm_nodes[slice(*segment.sm_range)]
    pms = ir.pm_nodes[slice(*segment.pm_range)]
    if len(sms) != 1 or len(pms) != 2:
        raise ValueError("exit-unshuffle footprint must contain one SM and two PM nodes")
    sm, p0, p1 = sms[0], pms[0], pms[1]
    nodes = (sm, p0, p1)
    if any(node.op != "FW_maybe_unshuffle" or len(node.ins) != 2 or len(node.outs) != 1 for node in nodes):
        raise ValueError("exit-unshuffle node signature mismatch")
    if tuple(node.rank for node in nodes) != (0, 0, 1) or tuple(node.params for node in nodes) != (
        [1, 0], [2, 0], [2, 1]
    ):
        raise ValueError("exit-unshuffle rank/params mismatch")
    metadata_tids = {node.ins[1] for node in nodes}
    if len(metadata_tids) != 1:
        raise ValueError("exit-unshuffle node metadata bindings disagree")
    actual_metadata_tid = next(iter(metadata_tids))

    records = {item.source: item for item in chain.relation_facts}
    if len(transition.pre_facts) != 1 or len(transition.post_facts) != 1:
        raise ValueError("exit-unshuffle requires one pre/post relation")
    pre = records[transition.pre_facts[0]]
    post = records[transition.post_facts[0]]
    if pre.kind != "zigzag" or post.kind != "ordinary" or post.metadata_tid is not None:
        raise ValueError("exit-unshuffle relation kinds mismatch")
    for fact, outputs in ((pre, False), (post, True)):
        tids = tuple(node.outs[0] if outputs else node.ins[0] for node in nodes)
        if tids != (fact.sm_tid, fact.pm_rank0_tid, fact.pm_rank1_tid):
            raise ValueError("exit-unshuffle fact roles do not match node TIDs")
    if pre.full_shape != post.full_shape or pre.shard_shape != post.shard_shape:
        raise ValueError("exit-unshuffle relation payload changed")
    if not pre.shard_shape:
        raise ValueError("exit-unshuffle shard shape must be nonempty")
    ldim, tail = pre.shard_shape[0], pre.shard_shape[1:]
    if ldim <= 0 or ldim % 2 != 0 or pre.full_shape != (ldim * 2, *tail):
        raise ValueError("exit-unshuffle shape is not an even two-rank dim-0 split")
    if pre.metadata_tid is None or pre.metadata_region_id is None:
        raise ValueError("exit-unshuffle input lacks decoded metadata provenance")

    authorities = list(chain.authority_facts)
    aliases = [
        fact for fact in authorities
        if fact.kind == "tensor_eq"
        and (fact.left_side, fact.left_tid, fact.right_side, fact.right_tid)
        == ("pm", pre.metadata_tid, "pm", actual_metadata_tid)
    ]
    if len(aliases) != 1:
        raise ValueError("exit-unshuffle metadata equality authority mismatch")
    alias = aliases[0]
    packed_facts = [
        fact for fact in authorities
        if fact.kind == "packed_cu"
        and (fact.side, fact.tid, fact.total_tokens, fact.num_ranks)
        == ("pm", actual_metadata_tid, ldim * 2, 2)
    ]
    if len(packed_facts) != 1:
        raise ValueError("exit-unshuffle PackedCu authority mismatch")
    packed = packed_facts[0]
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if not {pre.fact_id, alias.fact_id, packed.fact_id} <= set(before.fact_ids):
        raise ValueError("exit-unshuffle relation/metadata authority is not live")
    if post.fact_id not in after.fact_ids or not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("exit-unshuffle state delta mismatch")

    sm_graph, pm_graph = ir.sm_graph_ref, ir.pm_graph_ref
    sm_text, p0_text, p1_text = (_node_text(node) for node in nodes)
    fs, ss = _shape_text(post.full_shape), _shape_text(post.shard_shape)
    tail_text = _shape_text(list(tail))
    lines = [
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {sm_graph} {pm_graph} {before.state_id} {after.state_id} where",
        f"  smNodes := [{sm_text}]",
        f"  pmNodes := [{p0_text}, {p1_text}]",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := [{sm_text}]",
        f"    let pmNodes : List NodeDecl := [{p0_text}, {p1_text}]",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {sm_graph}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hIn : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hPacked : {packed.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hAlias : {alias.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    change ZigzagCollective.PackedCuSeqlensWF (pmStore {actual_metadata_tid}) {ldim * 2} 2 at hPacked",
        f"    change pmStore {pre.metadata_tid} = pmStore {actual_metadata_tid} at hAlias",
        f"    change GeneratedPatterns.Zigzag2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) (pmStore {pre.metadata_tid}) {fs} {ss} at hIn",
        "    rw [hAlias] at hIn",
        f"    have hDecoded : decodeCuSeqlens (pmStore {actual_metadata_tid}) = [0, 2 * {ldim}] := by",
        "      simpa only [Nat.reduceMul] using",
        "        (ZigzagCollective.PackedCuSeqlensWF.decoded_single hPacked)",
    ]

    def writer(name, graph, store, final, node, before_nodes, after_nodes, buddy_tids):
        prefix = f"[{', '.join(_node_text(item) for item in before_nodes)}]"
        buddies = f"[{', '.join(_node_text(item) for item in ((sm,) if node is sm else (p0, p1)))}]"
        def prefix_read(tid):
            if not before_nodes:
                return f"{store} {tid}"
            return f"{prefix}.foldl (applyNodeDistributedFaithful {graph}) {store} {tid}"
        values = ", ".join(prefix_read(tid) for tid in buddy_tids)
        expr = (
            f"ZigzagCollective.fw_maybe_unshuffle_collective [{values}] "
            f"(decodeCuSeqlens ({prefix_read(actual_metadata_tid)})) "
            f"{node.params[0]} {node.params[1]}"
        )
        base_values = ", ".join(f"{store} {tid}" for tid in buddy_tids)
        base_expr = (
            f"ZigzagCollective.fw_maybe_unshuffle_collective [{base_values}] "
            f"(decodeCuSeqlens ({store} {actual_metadata_tid})) "
            f"{node.params[0]} {node.params[1]}"
        )
        out = [
            f"    have {name} : {final} {node.outs[0]} = {base_expr} := by",
            "      calc",
            f"        {final} {node.outs[0]} = {expr} := by",
            f"          simpa [{final}, {'smNodes' if final == 'smFinal' else 'pmNodes'}] using",
            f"            (foldl_faithful_middle_writer {graph} {store} {prefix} [{', '.join(_node_text(item) for item in after_nodes)}] {_node_text(node)} {node.outs[0]}",
            f"              (fun t => ZigzagCollective.fw_maybe_unshuffle_collective [{', '.join(f't {tid}' for tid in buddy_tids)}] (decodeCuSeqlens (t {actual_metadata_tid})) {node.params[0]} {node.params[1]}) (by",
            "                intro t",
            "                rw [applyNodeDistributedFaithful_unshuffle_out]",
            "                unfold applyNodeFaithfulUnshuffleValue",
            f"                rw [show {graph}.replicaBuddies {_node_text(node)} = {buddies} by native_decide]",
            "                rfl) (by native_decide) (by native_decide))",
        ]
        if before_nodes:
            out += [f"        _ = {base_expr} := by"]
            for tid in dict.fromkeys((*buddy_tids, actual_metadata_tid)):
                out += [
                    f"          rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix} {store} {tid} (by native_decide) (by native_decide)]"
                ]
        else:
            out += ["        _ = _ := rfl"]
        return out

    lines += writer("hSmWriter", sm_graph, "smStore", "smFinal", sm, [], [], (sm.ins[0],))
    lines += writer("hPm0Writer", pm_graph, "pmStore", "pmFinal", p0, [], [p1], (p0.ins[0], p1.ins[0]))
    lines += writer("hPm1Writer", pm_graph, "pmStore", "pmFinal", p1, [p0], [], (p0.ins[0], p1.ins[0]))
    lines += [
        f"    have hSmOut : smFinal {sm.outs[0]} = smStore {sm.ins[0]} := by",
        "      rw [hSmWriter]",
        "      simp only [ZigzagCollective.fw_maybe_unshuffle_collective_cpSize_one, List.getD_cons_zero]",
        f"    have hCore : smStore {sm.ins[0]} = allGatherPrimDimN 0 2 0",
        f"        [ZigzagCollective.fw_maybe_unshuffle_collective [pmStore {p0.ins[0]}, pmStore {p1.ins[0]}] (decodeCuSeqlens (pmStore {actual_metadata_tid})) 2 0,",
        f"         ZigzagCollective.fw_maybe_unshuffle_collective [pmStore {p0.ins[0]}, pmStore {p1.ins[0]}] (decodeCuSeqlens (pmStore {actual_metadata_tid})) 2 1] := by",
        f"      exact GeneratedPatterns.Zigzag2Rel.unshuffle_gather_single {ldim} {tail_text} hIn",
        "        (by decide) (by decide) rfl hDecoded",
        f"    have hOut : {post.fact_id}.Holds smFinal pmFinal := by",
        f"      change GeneratedPatterns.Ordinary2Rel (smFinal {sm.outs[0]}) (pmFinal {p0.outs[0]}) (pmFinal {p1.outs[0]}) {fs} {ss}",
        "      refine {",
        "        full_value := ?_",
        "        full_shape := ?_",
        "        rank0_shape := ?_",
        "        rank1_shape := ?_",
        "      }",
        "      · rw [hSmOut, hPm0Writer, hPm1Writer]",
        "        exact hCore",
        "      · rw [hSmOut]",
        "        exact hIn.full_shape",
        "      · rw [hPm0Writer, ZigzagCollective.fw_maybe_unshuffle_collective_shape]",
        "        simp only [List.getD_cons_zero]",
        "        exact hIn.rank0_shape",
        "      · rw [hPm1Writer, ZigzagCollective.fw_maybe_unshuffle_collective_shape]",
        "        simp only [List.getD_cons_succ, List.getD_cons_zero]",
        "        exact hIn.rank1_shape",
        "    exact RelationState.Holds.mono_insert hframe hOut (by native_decide)",
        "",
    ]
    return "\n".join(lines)


def render_closed_ce_fst_segment(ir: GoalIR, relation, segment_id: str) -> str:
    """Render a closed two-rank InnerChunk CE loss projection terminal."""
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("CE .fst segment requires a complete closed chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("CE .fst segment must own one transition")
    transitions = {item.transition_id: item for item in relation.transition_specs}
    transition = transitions[segment.transition_ids[0]]
    if transition.rule_id != "inner-chunk-ce-projection-gather-two-rank" or transition.lean_theorem != (
        "TrainVerify.Denote.GeneratedPatterns.fw_inner_chunk_ce_fst_allGather0_commute_2_of"
    ):
        raise ValueError("segment is not the registered CE .fst family")
    if ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2:
        raise ValueError("CE .fst requires exact SM=1/PM=2 graph ranks")
    if transition.sm_node_indices != tuple(range(*segment.sm_range)) or transition.pm_node_indices != tuple(
        range(*segment.pm_range)
    ):
        raise ValueError("CE .fst transition/segment footprint mismatch")
    sms = ir.sm_nodes[slice(*segment.sm_range)]
    pms = ir.pm_nodes[slice(*segment.pm_range)]
    if len(sms) != 1 or len(pms) != 3:
        raise ValueError("CE .fst footprint must contain one SM and three PM nodes")
    sm, p0, p1, gather = sms[0], pms[0], pms[1], pms[2]
    ce_nodes = (sm, p0, p1)
    if any(node.op != "FW_inner_chunk_ce" or len(node.ins) != 3
           or len(node.outs) != 2 or not node.params for node in ce_nodes):
        raise ValueError("CE .fst node signature mismatch")
    if tuple(node.rank for node in ce_nodes) != (0, 0, 1) or any(
        node.params != sm.params for node in (p0, p1)
    ):
        raise ValueError("CE .fst ranks/parameters disagree")
    if (gather.op != "AllGatherPrim" or gather.rank != 0 or gather.params != [0]
            or gather.ins != [p0.outs[0], p1.outs[0]] or len(gather.outs) != 1):
        raise ValueError("CE .fst terminal gather mismatch")

    records = {item.source: item for item in chain.relation_facts}
    pre_records = [records.get(source) for source in transition.pre_facts]
    ordinary = [item for item in pre_records if item is not None and item.kind == "ordinary"]
    label_chunks = [item for item in pre_records if item is not None and item.kind == "label_chunks"]
    if len(ordinary) != 1:
        raise ValueError("CE .fst activation authority mismatch")
    if len(label_chunks) != 1:
        raise ValueError("CE .fst label-chunk authority mismatch")
    activation, chunks = ordinary[0], label_chunks[0]
    if len(transition.post_facts) != 1 or transition.post_facts[0] not in records:
        raise ValueError("CE .fst output fact mismatch")
    post = records[transition.post_facts[0]]
    if post.kind != "joined_ordinary" or post.joined_pm_tid != gather.outs[0]:
        raise ValueError("CE .fst output is not joined ordinary")
    if ((activation.sm_tid, activation.pm_rank0_tid, activation.pm_rank1_tid)
            != (sm.ins[0], p0.ins[0], p1.ins[0])):
        raise ValueError("CE .fst activation roles do not match node TIDs")
    if ((post.sm_tid, post.pm_rank0_tid, post.pm_rank1_tid)
            != (sm.outs[0], p0.outs[0], p1.outs[0])):
        raise ValueError("CE .fst output roles do not match node TIDs")
    full_label, local0, local1 = sm.ins[2], p0.ins[2], p1.ins[2]
    if (chunks.sm_tid, chunks.pm_rank0_tid, chunks.pm_rank1_tid) != (
        full_label, local0, local1
    ):
        raise ValueError("CE .fst label-chunk TIDs do not match node roles")
    if len(activation.shard_shape) != 2 or len(chunks.full_shape) != 1:
        raise ValueError("CE .fst activation/label rank mismatch")
    rows, hidden = activation.shard_shape
    if (rows <= 0 or hidden <= 0 or activation.full_shape != (rows * 2, hidden)
            or chunks.full_shape != (rows * 2,) or chunks.shard_shape != (rows,)
            or post.full_shape != (rows * 2,) or post.shard_shape != (rows,)):
        raise ValueError("CE .fst closed shapes disagree")
    weight = sm.ins[1]
    if (p0.ins[1], p1.ins[1]) != (weight, weight):
        raise ValueError("CE .fst weight is not replicated")

    authorities = list(chain.authority_facts)
    def authority_one(kind, predicate, label):
        matches = [item for item in authorities if item.kind == kind and predicate(item)]
        if len(matches) != 1:
            raise ValueError(f"CE .fst {label} authority mismatch")
        return matches[0]
    weight_eq = authority_one("tensor_eq", lambda x:
        (x.left_side, x.left_tid, x.right_side, x.right_tid) == ("sm", weight, "pm", weight), "weight equality")
    weight_shape = authority_one("tensor_shape", lambda x:
        (x.side, x.tid) == ("pm", weight), "weight shape")
    if len(weight_shape.shape) != 2 or weight_shape.shape[1] != hidden:
        raise ValueError("CE .fst weight dimensions disagree")
    vocab = weight_shape.shape[0]
    label_eq = authority_one("tensor_eq", lambda x:
        (x.left_side, x.left_tid, x.right_side, x.right_tid) == ("sm", full_label, "pm", full_label), "label equality")
    label_shape = authority_one("tensor_shape", lambda x:
        (x.side, x.tid) == ("pm", full_label), "label shape")
    label_bound = authority_one("label_bound", lambda x:
        (x.side, x.tid, x.length, x.upper_bound) == ("pm", full_label, rows * 2, vocab), "label bound")
    if tuple(label_shape.shape) != chunks.full_shape:
        raise ValueError("CE .fst label shape authority disagrees")
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {activation.fact_id, chunks.fact_id, weight_eq.fact_id, weight_shape.fact_id,
                label_eq.fact_id, label_shape.fact_id, label_bound.fact_id}
    if not required <= set(before.fact_ids):
        raise ValueError("CE .fst required authority is not live")
    if post.fact_id not in after.fact_ids or not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("CE .fst state delta mismatch")

    sm_graph, pm_graph = ir.sm_graph_ref, ir.pm_graph_ref
    sm_text, p0_text, p1_text, gather_text = (_node_text(node) for node in (sm, p0, p1, gather))
    params_text = "[" + ", ".join(str(value) for value in sm.params) + "]"
    zscale = f"((({params_text}.getD 1 0 : Nat) : Scalar))"
    def ce_expr(store, node):
        return (f"(fw_inner_chunk_ce ({store} {node.ins[0]}) ({store} {node.ins[1]}) "
                f"({store} {node.ins[2]}) ((({store} {node.ins[1]}).shape.head?).getD 0) {zscale}).fst")
    sm_nodes_text = f"[{sm_text}]"
    pm_nodes_text = f"[{p0_text}, {p1_text}, {gather_text}]"
    lines = [
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {sm_graph} {pm_graph} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_text}", f"  pmNodes := {pm_nodes_text}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := {sm_nodes_text}",
        f"    let pmNodes : List NodeDecl := {pm_nodes_text}",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {sm_graph}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hActivation : {activation.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hChunks : {chunks.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hWeightEq : {weight_eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hWeightShape : {weight_shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hLabelEq : {label_eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hLabelShape : {label_shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hLabelBound : {label_bound.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    change GeneratedPatterns.Ordinary2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) {_shape_text(activation.full_shape)} {_shape_text(activation.shard_shape)} at hActivation",
        f"    change pmStore {local0} = chunkPrimDimN 0 2 0 (pmStore {full_label}) ∧ pmStore {local1} = chunkPrimDimN 0 2 1 (pmStore {full_label}) ∧ _ at hChunks",
        f"    change smStore {weight} = pmStore {weight} at hWeightEq",
        f"    change (pmStore {weight}).shape = {_shape_text(weight_shape.shape)} at hWeightShape",
        f"    change smStore {full_label} = pmStore {full_label} at hLabelEq",
        f"    change (pmStore {full_label}).shape = {_shape_text(label_shape.shape)} at hLabelShape",
        f"    change (∀ index < {rows * 2}, scalarToNat (valAt (pmStore {full_label}) index) < {vocab}) at hLabelBound",
    ]

    def writer(name, graph, store, final, node, before_nodes, after_nodes):
        prefix = f"[{', '.join(_node_text(item) for item in before_nodes)}]"
        prefix_store = store if not before_nodes else f"{prefix}.foldl (applyNodeDistributedFaithful {graph}) {store}"
        prefix_expr = ce_expr(prefix_store, node)
        base_expr = ce_expr(store, node)
        out = [
            f"    have {name} : {final} {node.outs[0]} = {base_expr} := by", "      calc",
            f"        {final} {node.outs[0]} = {prefix_expr} := by",
            f"          simpa [{final}, {'smNodes' if final == 'smFinal' else 'pmNodes'}] using",
            f"            (foldl_faithful_middle_writer {graph} {store} {prefix} [{', '.join(_node_text(item) for item in after_nodes)}] {_node_text(node)} {node.outs[0]}",
            f"              (fun t => {ce_expr('t', node)}) (by",
            "                intro t",
            "                rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "                  (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "                simp [applyNodeDistributed, applyNodeRingAttn]",
            f"                exact applyNode_fw_inner_chunk_ce_fst_out_1p {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} {params_text})",
            "              (by native_decide) (by native_decide))",
        ]
        if before_nodes:
            out.append(f"        _ = {base_expr} := by")
            for tid in dict.fromkeys(node.ins):
                out.append(f"          rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix} {store} {tid} (by native_decide) (by native_decide)]")
        else:
            out.append("        _ = _ := rfl")
        return out

    lines += writer("hSmWriter", sm_graph, "smStore", "smFinal", sm, [], [])
    lines += writer("hPm0Writer", pm_graph, "pmStore", "pmFinal", p0, [], [p1, gather])
    lines += writer("hPm1Writer", pm_graph, "pmStore", "pmFinal", p1, [p0], [gather])
    lines += [
        f"    have hGatherWriter : pmFinal {gather.outs[0]} = allGatherPrimDimN 0 2 0 [pmFinal {gather.ins[0]}, pmFinal {gather.ins[1]}] := by",
        f"      have hWriter : pmFinal {gather.outs[0]} = allGatherPrimDimN 0 2 0 [([{p0_text}, {p1_text}].foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[0]}, ([{p0_text}, {p1_text}].foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[1]}] := by",
        "        unfold pmFinal pmNodes",
        f"        exact foldl_faithful_middle_writer {pm_graph} pmStore [{p0_text}, {p1_text}] [] {gather_text} {gather.outs[0]}",
        f"          (fun t => allGatherPrimDimN 0 2 0 [t {gather.ins[0]}, t {gather.ins[1]}]) (by",
        "            intro t",
        "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "              (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
        "            simp [applyNodeDistributed, applyNodeRingAttn]",
        f"            exact applyNode_allGatherPrimDimN_out {pm_graph} t 0 [{gather.ins[0]}, {gather.ins[1]}] {gather.outs[0]} 0)",
        "          (by native_decide) (by native_decide)",
        f"      have h0 := foldl_faithful_prefix_read_eq_final {pm_graph} pmStore [{p0_text}, {p1_text}] [{gather_text}] {gather.ins[0]} (by native_decide) (by native_decide)",
        f"      have h1 := foldl_faithful_prefix_read_eq_final {pm_graph} pmStore [{p0_text}, {p1_text}] [{gather_text}] {gather.ins[1]} (by native_decide) (by native_decide)",
        "      change _ = pmFinal _ at h0 h1",
        "      rw [h0, h1] at hWriter", "      exact hWriter",
    ]
    lines += [
        f"    have hVocab : (((pmStore {weight}).shape.head?).getD 0) = {vocab} := by",
        "      rw [hWeightShape]", "      rfl",
        "    have hCore := GeneratedPatterns.fw_inner_chunk_ce_fst_allGather0_commute_2_of",
        f"      (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) (pmStore {weight}) (pmStore {full_label})",
        f"      {rows} {hidden} {vocab} (by decide) (by decide) (by decide)",
        "      hActivation.rank0_shape hActivation.rank1_shape hWeightShape",
        "      (by simpa only [Nat.reduceMul] using hLabelShape) hLabelBound " + zscale,
        f"    have hOut : {post.fact_id}.Holds smFinal pmFinal := by",
        f"      change JoinedOrdinary2Rel (smFinal {sm.outs[0]}) (pmFinal {p0.outs[0]}) (pmFinal {p1.outs[0]}) (pmFinal {gather.outs[0]}) {_shape_text(post.full_shape)} {_shape_text(post.shard_shape)}",
        "      have hOrdinary : GeneratedPatterns.Ordinary2Rel",
        f"          (smFinal {sm.outs[0]}) (pmFinal {p0.outs[0]}) (pmFinal {p1.outs[0]}) {_shape_text(post.full_shape)} {_shape_text(post.shard_shape)} := by",
        "        refine {", "          full_value := ?_", "          full_shape := ?_",
        "          rank0_shape := ?_", "          rank1_shape := ?_", "        }",
        "        · rw [hSmWriter, hPm0Writer, hPm1Writer, hWeightEq, hLabelEq, hChunks.1, hChunks.2.1, hVocab]",
        "          rw [hActivation.full_value]",
        "          exact hCore",
        "        · rw [hSmWriter]",
        f"          exact fw_inner_chunk_ce_fst_shape _ _ _ _ _ {rows * 2} (by rw [hActivation.full_shape]; rfl)",
        "        · rw [hPm0Writer]",
        f"          exact fw_inner_chunk_ce_fst_shape _ _ _ _ _ {rows} (by rw [hActivation.rank0_shape]; rfl)",
        "        · rw [hPm1Writer]",
        f"          exact fw_inner_chunk_ce_fst_shape _ _ _ _ _ {rows} (by rw [hActivation.rank1_shape]; rfl)",
        "      refine { toOrdinary2Rel := hOrdinary, joined_value := hGatherWriter, public_value := ?_ }",
        "      exact hOrdinary.full_value.trans hGatherWriter.symm",
        "    exact RelationState.Holds.mono_insert hframe hOut (by native_decide)", "",
    ]
    return "\n".join(lines)

def render_closed_indexed_stack_segment(ir: GoalIR, relation, segment_id: str) -> str:
    """Render an ordered dim-1 indexed stack with one fold per authority axis."""
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("indexed-stack segment requires a complete closed chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("indexed-stack segment must own one transition")
    transitions = {item.transition_id: item for item in relation.transition_specs}
    transition = transitions[segment.transition_ids[0]]
    if transition.rule_id != "indexed-stack-gather-two-rank" or transition.lean_theorem != (
        "TrainVerify.Denote.RelationCompiler.fw_stack_allGather0_dim1_commute_2d_element"
    ):
        raise ValueError("segment is not the registered indexed-stack family")
    if ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2:
        raise ValueError("indexed stack requires exact SM=1/PM=2 graph ranks")
    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != 3:
        raise ValueError("indexed-stack transition footprint mismatch")
    sm_index = transition.sm_node_indices[0]
    pm0_index, pm1_index, gather_index = transition.pm_node_indices
    if not (segment.sm_range[0] <= sm_index < segment.sm_range[1]) or any(
        not segment.pm_range[0] <= index < segment.pm_range[1]
        for index in transition.pm_node_indices
    ):
        raise ValueError("indexed-stack writers escape their atomic segment")
    sm, p0, p1, gather = (
        ir.sm_nodes[sm_index], ir.pm_nodes[pm0_index],
        ir.pm_nodes[pm1_index], ir.pm_nodes[gather_index],
    )
    stacks = (sm, p0, p1)
    if any(node.op != "FW_stack" or len(node.outs) != 1 or node.params for node in stacks):
        raise ValueError("indexed-stack writer signature mismatch")
    if tuple(node.rank for node in stacks) != (0, 0, 1):
        raise ValueError("indexed-stack writer rank order mismatch")
    if (gather.op, gather.rank, gather.ins, gather.outs, gather.params) != (
        "AllGatherPrim", 0, [p0.outs[0], p1.outs[0]], [sm.outs[0]], [1]
    ):
        raise ValueError("indexed-stack gather signature mismatch")

    records = {item.source: item for item in chain.relation_facts}
    if len(transition.pre_facts) == 0 or any(source not in records for source in transition.pre_facts):
        raise ValueError("indexed stack lacks closed source relations")
    unordered_sources = [records[source] for source in transition.pre_facts]
    if any(item.kind != "ordinary" for item in unordered_sources):
        raise ValueError("indexed stack consumes non-ordinary source relations")
    if len(transition.post_facts) != 1 or transition.post_facts[0] not in records:
        raise ValueError("indexed stack lacks one closed post fact")
    post = records[transition.post_facts[0]]
    if (post.kind != "joined_indexed_stack_dim1" or post.gather_dim != 1
            or post.joined_pm_tid != gather.outs[0]):
        raise ValueError("indexed stack post relation is not truthful joined dim-1")
    ordered_specs = tuple(
        type(transition.pre_facts[0])("ordinary", refs)
        for refs in post.source.source_step_triples
    )
    if set(ordered_specs) != set(transition.pre_facts):
        raise ValueError("indexed stack post witnesses disagree with transition inputs")
    sources = [records[source] for source in ordered_specs]
    if len(sources) != len(post.source_tid_triples) or not sources:
        raise ValueError("indexed stack source witness count mismatch")
    expected_sources = tuple(
        (item.sm_tid, item.pm_rank0_tid, item.pm_rank1_tid) for item in sources
    )
    if post.source_tid_triples != expected_sources:
        raise ValueError("indexed stack materialized witnesses lost source order")
    if tuple(sm.ins) != tuple(item.sm_tid for item in sources) or tuple(p0.ins) != tuple(
        item.pm_rank0_tid for item in sources
    ) or tuple(p1.ins) != tuple(item.pm_rank1_tid for item in sources):
        raise ValueError("indexed stack writer inputs do not match ordered source facts")
    if (post.sm_tid, post.pm_rank0_tid, post.pm_rank1_tid) != (
        sm.outs[0], p0.outs[0], p1.outs[0]
    ):
        raise ValueError("indexed stack output fact does not match stack writers")
    if len(post.full_shape) != 3 or len(post.shard_shape) != 3:
        raise ValueError("indexed stack output shapes must be rank three")
    n, full_rows, width = post.full_shape
    shard_n, shard_rows, shard_width = post.shard_shape
    if (n, shard_n, width, shard_width, full_rows) != (
        len(sources), len(sources), width, width, 2 * shard_rows
    ) or shard_rows <= 0 or width <= 0:
        raise ValueError("indexed stack output shapes are not a positive dim-1 gather")
    if any(item.full_shape != (full_rows, width) or item.shard_shape != (shard_rows, width)
           for item in sources):
        raise ValueError("indexed stack source shapes do not match output tails")

    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    source_ids = {item.fact_id for item in sources}
    if not source_ids <= set(before.fact_ids):
        raise ValueError("indexed stack source relations are not live")
    if post.fact_id not in after.fact_ids or not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("indexed stack state delta mismatch")

    sm_graph, pm_graph = ir.sm_graph_ref, ir.pm_graph_ref
    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    sm_nodes_text = "[" + ", ".join(_node_text(node) for node in sm_nodes) + "]"
    pm_nodes_text = "[" + ", ".join(_node_text(node) for node in pm_nodes) + "]"
    prefix = segment.segment_id
    sm_nodes_name, pm_nodes_name = f"{prefix}_smNodes", f"{prefix}_pmNodes"
    sm_final_name, pm_final_name = f"{prefix}_smFinal", f"{prefix}_pmFinal"
    frame_name = f"{prefix}_frame"
    writer_bundle_name = f"{prefix}_writer_values_source_preservation"
    semantic_name = f"{prefix}_indexed_stack_semantic"
    gather_writer_name = f"{prefix}_gather_writer_value"
    sm_final = f"({sm_final_name} smStore)"
    pm_final = f"({pm_final_name} pmStore)"
    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := {sm_nodes_text}",
        f"private def {pm_nodes_name} : List NodeDecl := {pm_nodes_text}",
        f"@[irreducible] private def {sm_final_name} (smStore : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {sm_graph}) smStore",
        f"@[irreducible] private def {pm_final_name} (pmStore : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore", "",
        f"private theorem {frame_name} (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {before.state_id}.Holds {sm_final} {pm_final} := by",
        f"  unfold {sm_final_name} {pm_final_name}",
        f"  apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "  · native_decide", "  · native_decide", "  · native_decide", "  · native_decide", "",
    ]

    def writer(name, graph, store, final, final_name, nodes_name, all_nodes, absolute_index, node):
        position = absolute_index - (segment.sm_range[0] if graph == sm_graph else segment.pm_range[0])
        prefix_nodes, suffix_nodes = all_nodes[:position], all_nodes[position + 1:]
        prefix_nodes_text = "[" + ", ".join(_node_text(item) for item in prefix_nodes) + "]"
        suffix_nodes_text = "[" + ", ".join(_node_text(item) for item in suffix_nodes) + "]"
        target = _node_text(node)
        ins_text = "[" + ", ".join(str(tid) for tid in node.ins) + "]"
        prefix_store = store if not prefix_nodes else f"({prefix_nodes_text}.foldl (applyNodeDistributedFaithful {graph}) {store})"
        prefix_expr = f"fw_stack ({ins_text}.map {prefix_store})"
        base_expr = f"fw_stack ({ins_text}.map {store})"
        out = [
            f"  have {name} : {final} {node.outs[0]} = {base_expr} := by", "    calc",
            f"      {final} {node.outs[0]} = {prefix_expr} := by",
            f"        simpa [{final_name}, {nodes_name}] using",
            f"          (foldl_faithful_middle_writer {graph} {store} {prefix_nodes_text} {suffix_nodes_text} {target} {node.outs[0]}",
            f"            (fun t => fw_stack ({ins_text}.map t)) (by",
            "              intro t",
            "              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "                (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "              simp [applyNodeDistributed, applyNodeRingAttn]",
            f"              exact applyNode_fw_stack_out {graph} t {node.rank} {ins_text} {node.outs[0]} [])",
            "            (by native_decide) (by native_decide))",
        ]
        if prefix_nodes:
            out.append(f"      _ = {base_expr} := by")
            out.append("        simp only [List.map]")
            for tid in node.ins:
                out.append(
                    f"        rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix_nodes_text} {store} {tid} (by native_decide) (by native_decide)]"
                )
        else:
            out.append("      _ = _ := rfl")
        out += [
            f"  have {name}Sources : {ins_text}.map {final} = {ins_text}.map {store} := by",
            "    apply List.map_congr_left", "    intro tid htid",
            f"    have hread := foldl_applyNodeDistributedFaithful_at_not_written {graph} {nodes_name} {store} tid (by native_decide) (by",
            "      simp only [List.mem_cons, List.not_mem_nil, or_false] at htid",
            f"      rcases htid with {' | '.join(f'h{index}' for index in range(len(node.ins)))}",
            "      all_goals subst tid",
            "      all_goals native_decide)",
            f"    simpa [{final_name}] using hread",
            f"  rw [← {name}Sources] at {name}",
        ]
        return out, ins_text

    sm_writer, sm_ins_text = writer("hSmWriter", sm_graph, "smStore", sm_final,
                                    sm_final_name, sm_nodes_name, sm_nodes, sm_index, sm)
    pm0_writer, pm0_ins_text = writer("hPm0Writer", pm_graph, "pmStore", pm_final,
                                      pm_final_name, pm_nodes_name, pm_nodes, pm0_index, p0)
    pm1_writer, pm1_ins_text = writer("hPm1Writer", pm_graph, "pmStore", pm_final,
                                      pm_final_name, pm_nodes_name, pm_nodes, pm1_index, p1)
    lines += [
        f"private theorem {writer_bundle_name} (smStore pmStore : Store) :",
        f"    {sm_final} {sm.outs[0]} = fw_stack ({sm_ins_text}.map {sm_final}) ∧",
        f"    {pm_final} {p0.outs[0]} = fw_stack ({pm0_ins_text}.map {pm_final}) ∧",
        f"    {pm_final} {p1.outs[0]} = fw_stack ({pm1_ins_text}.map {pm_final}) ∧",
        f"    {sm_ins_text}.map {sm_final} = {sm_ins_text}.map smStore ∧",
        f"    {pm0_ins_text}.map {pm_final} = {pm0_ins_text}.map pmStore ∧",
        f"    {pm1_ins_text}.map {pm_final} = {pm1_ins_text}.map pmStore := by",
    ]
    lines += sm_writer + pm0_writer + pm1_writer
    lines += [
        "  exact ⟨hSmWriter, hPm0Writer, hPm1Writer, hSmWriterSources,",
        "    hPm0WriterSources, hPm1WriterSources⟩", "",
    ]

    for index, fact in enumerate(sources):
        source_name = f"{prefix}_source_{index:02d}"
        lines += [
            f"private theorem {source_name} (smStore pmStore : Store)",
            f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
            f"    GeneratedPatterns.Ordinary2Rel ({sm_final} {fact.sm_tid})",
            f"      ({pm_final} {fact.pm_rank0_tid}) ({pm_final} {fact.pm_rank1_tid})",
            f"      {_shape_text(fact.full_shape)} {_shape_text(fact.shard_shape)} := by",
            f"  have hframe := {frame_name} smStore pmStore hstate",
            f"  have hSource : {fact.fact_id}.Holds {sm_final} {pm_final} :=",
            "    hframe _ (by native_decide)",
            f"  change GeneratedPatterns.Ordinary2Rel ({sm_final} {fact.sm_tid})",
            f"    ({pm_final} {fact.pm_rank0_tid}) ({pm_final} {fact.pm_rank1_tid})",
            f"    {_shape_text(fact.full_shape)} {_shape_text(fact.shard_shape)} at hSource",
            "  exact hSource", "",
        ]

    triples = "[" + ", ".join(
        f"({sm_final} {fact.sm_tid}, {pm_final} {fact.pm_rank0_tid}, {pm_final} {fact.pm_rank1_tid})"
        for fact in sources
    ) + "]"
    rank0_values = "[" + ", ".join(f"{pm_final} {fact.pm_rank0_tid}" for fact in sources) + "]"
    rank1_values = "[" + ", ".join(f"{pm_final} {fact.pm_rank1_tid}" for fact in sources) + "]"
    full_values = "[" + ", ".join(f"{sm_final} {fact.sm_tid}" for fact in sources) + "]"
    alternatives = " | ".join(f"h{index:02d}" for index in range(len(sources)))
    exacts = " | ".join(f"exact hSource{index:02d}" for index in range(len(sources)))
    source_relations_name = f"{prefix}_ordered_source_relations"
    rank0_shapes_name = f"{prefix}_rank0_shapes"
    rank1_shapes_name = f"{prefix}_rank1_shapes"
    commute_name = f"{prefix}_source_commute"
    reconstruction_name = f"{prefix}_ordered_reconstruction"
    state_name = f"{prefix}_publish_state"

    gather_position = gather_index - segment.pm_range[0]
    gather_before = pm_nodes[:gather_position]
    gather_after = pm_nodes[gather_position + 1:]
    gather_before_text = "[" + ", ".join(_node_text(item) for item in gather_before) + "]"
    gather_after_text = "[" + ", ".join(_node_text(item) for item in gather_after) + "]"
    gather_suffix_text = "[" + ", ".join(_node_text(item) for item in (gather, *gather_after)) + "]"
    gather_text = _node_text(gather)
    lines += [
        f"private theorem {gather_writer_name} (pmStore : Store) :",
        f"    {pm_final} {gather.outs[0]} = allGatherPrimDimN 1 2 0",
        f"      [{pm_final} {gather.ins[0]}, {pm_final} {gather.ins[1]}] := by",
        f"  have hWriter : {pm_final} {gather.outs[0]} = allGatherPrimDimN 1 2 0",
        f"      [({gather_before_text}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[0]},",
        f"       ({gather_before_text}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[1]}] := by",
        f"    unfold {pm_final_name}",
        f"    rw [show {pm_nodes_name} = {gather_before_text} ++ [{gather_text}] ++ {gather_after_text} by native_decide]",
        f"    exact foldl_faithful_middle_writer {pm_graph} pmStore {gather_before_text} {gather_after_text} {gather_text} {gather.outs[0]}",
        f"      (fun t => allGatherPrimDimN 1 2 0 [t {gather.ins[0]}, t {gather.ins[1]}]) (by",
        "        intro t",
        "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "          (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]",
        "        unfold applyNodeDistributed", "        rw [if_neg (by decide)]",
        "        rw [applyNodeRingAttn_eq_applyNode_of_not_ring]",
        f"        · exact applyNode_allGatherPrimDimN_out {pm_graph} t {gather.rank} [{gather.ins[0]}, {gather.ins[1]}] {gather.outs[0]} 1",
        "        · decide", "        · decide",
        "      ) (by native_decide) (by native_decide)",
        f"  have h0Raw := foldl_faithful_prefix_read_eq_final {pm_graph} pmStore {gather_before_text} {gather_suffix_text} {gather.ins[0]} (by native_decide) (by native_decide)",
        f"  have h1Raw := foldl_faithful_prefix_read_eq_final {pm_graph} pmStore {gather_before_text} {gather_suffix_text} {gather.ins[1]} (by native_decide) (by native_decide)",
        f"  have h0 : ({gather_before_text}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[0]} = {pm_final} {gather.ins[0]} := by",
        f"    rw [{pm_final_name}]",
        "    exact h0Raw",
        f"  have h1 : ({gather_before_text}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[1]} = {pm_final} {gather.ins[1]} := by",
        f"    rw [{pm_final_name}]",
        "    exact h1Raw",
        "  rw [h0, h1] at hWriter", "  exact hWriter", "",
        f"private theorem {source_relations_name} (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    ∀ source ∈ {triples},",
        f"      GeneratedPatterns.Ordinary2Rel source.1 source.2.1 source.2.2 [{full_rows}, {width}] [{shard_rows}, {width}] := by",
    ]
    for index in range(len(sources)):
        lines.append(f"  have hSource{index:02d} := {prefix}_source_{index:02d} smStore pmStore hstate")
    lines += [
        "  intro source hsource",
        "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsource",
        f"  rcases hsource with {alternatives}",
        "  all_goals subst source",
        f"  all_goals first | {exacts}", "",
    ]
    helper_specs = (
        (rank0_shapes_name, rank0_values, f"zeroTensor [{shard_rows}, {width}]", f"[{shard_rows}, {width}]", "rank0_shape"),
        (rank1_shapes_name, rank1_values, f"zeroTensor [{shard_rows}, {width}]", f"[{shard_rows}, {width}]", "rank1_shape"),
    )
    for helper_name, values, fallback, shape, projection in helper_specs:
        lines += [
            f"private theorem {helper_name} (smStore pmStore : Store)",
            f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
            f"    ∀ i (_ : i < {n}), ({values}.getD i ({fallback})).shape = {shape} := by",
        ]
        for index in range(len(sources)):
            lines.append(f"  have hSource{index:02d} := {prefix}_source_{index:02d} smStore pmStore hstate")
        lines += [
            "  intro i hi",
            "  interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ]",
            f"  all_goals first | {' | '.join(f'exact hSource{index:02d}.{projection}' for index in range(len(sources)))}",
            "",
        ]
    lines += [
        f"private theorem {commute_name} (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    ∀ i (_ : i < {n}),",
        f"      {full_values}.getD i (zeroTensor [{full_rows}, {width}]) =",
        f"      allGatherPrimDimN 0 2 0 [{rank0_values}.getD i (zeroTensor [{shard_rows}, {width}]),",
        f"        {rank1_values}.getD i (zeroTensor [{shard_rows}, {width}])] := by",
    ]
    for index in range(len(sources)):
        lines.append(f"  have hSource{index:02d} := {prefix}_source_{index:02d} smStore pmStore hstate")
    lines += [
        "  intro i hi",
        "  interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ]",
        f"  all_goals first | {' | '.join(f'exact hSource{index:02d}.full_value' for index in range(len(sources)))}",
        "",
        f"private theorem {reconstruction_name} (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    fw_stack {full_values} =",
        f"      allGatherPrimDimN 1 2 0 [fw_stack {rank0_values}, fw_stack {rank1_values}] := by",
    ]
    for index in range(len(sources)):
        lines.append(f"  have hSource{index:02d} := {prefix}_source_{index:02d} smStore pmStore hstate")
    lines += [
        f"  exact fw_stack_allGather0_dim1_commute_2d_element {n} {shard_rows} {width}",
        "    (by decide) (by decide)",
        f"    {rank0_values}", f"    {rank1_values}", f"    {full_values}",
        "    (by rfl) (by rfl) (by rfl)",
        "    (by", f"      change ({pm_final} {sources[0].pm_rank0_tid}).shape = [{shard_rows}, {width}]",
        "      exact hSource00.rank0_shape)",
        "    (by", f"      change ({pm_final} {sources[0].pm_rank1_tid}).shape = [{shard_rows}, {width}]",
        "      exact hSource00.rank1_shape)",
        "    (by", f"      change ({sm_final} {sources[0].sm_tid}).shape = [{full_rows}, {width}]",
        "      exact hSource00.full_shape)",
    ]
    lines += [
        f"    ({rank0_shapes_name} smStore pmStore hstate)",
        f"    ({rank1_shapes_name} smStore pmStore hstate)",
        f"    ({commute_name} smStore pmStore hstate)",
        "",
    ]

    lines += [
        f"private theorem {semantic_name} (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    JoinedIndexedStack2Rel ({sm_final} {sm.outs[0]}) ({pm_final} {p0.outs[0]})",
        f"      ({pm_final} {p1.outs[0]}) ({pm_final} {gather.outs[0]}) {triples} 1 {_shape_text(post.full_shape)} {_shape_text(post.shard_shape)} := by",
        f"  rcases {writer_bundle_name} smStore pmStore with",
        "    ⟨hSmWriter, hPm0Writer, hPm1Writer, hSmSources, hPm0Sources, hPm1Sources⟩",
        f"  have hSource00 := {prefix}_source_00 smStore pmStore hstate",
        f"  have hGatherWriter := {gather_writer_name} pmStore",
        "  have hIndexed : IndexedStack2Rel",
        f"      ({sm_final} {sm.outs[0]}) ({pm_final} {p0.outs[0]}) ({pm_final} {p1.outs[0]}) {triples} 1 {_shape_text(post.full_shape)} {_shape_text(post.shard_shape)} := by",
        "    refine {", "      gather_dim := rfl", "      full_value := ?_",
        "      full_shape := ?_", "      rank0_shape := ?_", "      rank1_shape := ?_",
        "      full_stack := hSmWriter", "      rank0_stack := hPm0Writer",
        "      rank1_stack := hPm1Writer",
        f"      source_relations := {source_relations_name} smStore pmStore hstate", "    }",
        "    · rw [hSmWriter, hPm0Writer, hPm1Writer]",
        f"      exact {reconstruction_name} smStore pmStore hstate",
        "    · rw [hSmWriter]", f"      apply fw_stack_shape _ [{full_rows}, {width}]", f"      change ({sm_final} {sources[0].sm_tid}).shape = [{full_rows}, {width}]", "      exact hSource00.full_shape",
        "    · rw [hPm0Writer]", f"      apply fw_stack_shape _ [{shard_rows}, {width}]", f"      change ({pm_final} {sources[0].pm_rank0_tid}).shape = [{shard_rows}, {width}]", "      exact hSource00.rank0_shape",
        "    · rw [hPm1Writer]", f"      apply fw_stack_shape _ [{shard_rows}, {width}]", f"      change ({pm_final} {sources[0].pm_rank1_tid}).shape = [{shard_rows}, {width}]", "      exact hSource00.rank1_shape",
        "  refine { toIndexedStack2Rel := hIndexed, joined_value := hGatherWriter, public_value := ?_ }",
        "  exact hIndexed.full_value.trans hGatherWriter.symm", "",
        f"private theorem {state_name} (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds {sm_final} {pm_final} := by",
        f"  have hframe := {frame_name} smStore pmStore hstate",
        f"  have hOut : {post.fact_id}.Holds {sm_final} {pm_final} := by",
        f"    change JoinedIndexedStack2Rel ({sm_final} {sm.outs[0]}) ({pm_final} {p0.outs[0]}) ({pm_final} {p1.outs[0]}) ({pm_final} {gather.outs[0]}) {triples} 1 {_shape_text(post.full_shape)} {_shape_text(post.shard_shape)}",
        f"    exact {semantic_name} smStore pmStore hstate",
        "  exact RelationState.Holds.mono_insert hframe hOut (by native_decide)", "",
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {sm_graph} {pm_graph} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    simpa [{sm_final_name}, {pm_final_name}] using ({state_name} smStore pmStore hstate)", "",
    ]
    return "\n".join(lines)



def render_closed_topk_unshuffle_segment(ir: GoalIR, relation, segment_id: str) -> str:
    """Render a synchronized top-k projection followed by faithful unshuffle."""
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("top-k unshuffle renderer requires a complete closed chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("top-k unshuffle segment must own one transition")
    transition = {item.transition_id: item for item in relation.transition_specs}[
        segment.transition_ids[0]
    ]
    if (
        transition.rule_id != "zigzag-topk-unshuffle-two-rank"
        or transition.lean_theorem
        != "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.unshuffle_gather_single"
        or len(transition.pre_facts) != 1
        or len(transition.post_facts) != 1
    ):
        raise ValueError("segment is not the registered top-k unshuffle family")
    synchronized = [
        item
        for item in relation.synchronized_steps
        if item.rule_id == transition.rule_id
        and item.input_step_triple == transition.pre_facts[0].step_triple
        and item.output_step_triple == transition.post_facts[0].step_triple
    ]
    if len(synchronized) != 1:
        raise ValueError("top-k unshuffle lacks one exact synchronized step")
    synchronized = synchronized[0]
    projection_specs = {
        ".2.1": (1, "topk_routing_map", "map", " (by decide)"),
        ".2.2": (2, "topk_routing_gate_scores", "scores", " (by decide) (by decide)"),
    }
    if synchronized.output_projection not in projection_specs:
        raise ValueError("top-k unshuffle projection role is unsupported")
    projection, theorem_name, lemma_name, lemma_extra = projection_specs[
        synchronized.output_projection
    ]
    expected_topk_theorem = (
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel." + theorem_name
    )
    if synchronized.lean_theorems != (expected_topk_theorem, transition.lean_theorem):
        raise ValueError("top-k unshuffle theorem registration mismatch")
    if ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2:
        raise ValueError("top-k unshuffle requires exact SM=1/PM=2 graph ranks")

    records = {item.source: item for item in chain.relation_facts}
    pre, post = records[transition.pre_facts[0]], records[transition.post_facts[0]]
    if (
        pre.kind != "zigzag"
        or post.kind != "ordinary"
        or pre.metadata_tid is None
        or pre.metadata_region_id is None
        or post.metadata_tid is not None
        or pre.full_shape != post.full_shape
        or pre.shard_shape != post.shard_shape
        or len(pre.shard_shape) != 2
        or pre.full_shape != (2 * pre.shard_shape[0], pre.shard_shape[1])
    ):
        raise ValueError("top-k unshuffle relation payload mismatch")
    rows, num_experts = pre.shard_shape
    if rows <= 0 or rows % 2 != 0 or num_experts <= 0:
        raise ValueError("top-k unshuffle shape is not admissible")

    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    sm_start, pm_start = segment.sm_range[0], segment.pm_range[0]
    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != 2:
        raise ValueError("top-k unshuffle semantic ownership mismatch")
    unshuffle_indices = (*transition.sm_node_indices, *transition.pm_node_indices)
    usm = ir.sm_nodes[transition.sm_node_indices[0]]
    up0, up1 = (ir.pm_nodes[index] for index in transition.pm_node_indices)
    unodes = (usm, up0, up1)
    if (
        tuple(node.rank for node in unodes) != (0, 0, 1)
        or any(
            node.op != "FW_maybe_unshuffle"
            or len(node.ins) != 2
            or len(node.outs) != 1
            for node in unodes
        )
        or tuple(node.params for node in unodes) != ([1, 0], [2, 0], [2, 1])
        or len(set(unshuffle_indices)) != 3
    ):
        raise ValueError("top-k unshuffle node roles mismatch")
    actual_metadata = {node.ins[1] for node in unodes}
    if len(actual_metadata) != 1 or synchronized.metadata_tid not in actual_metadata:
        raise ValueError("top-k unshuffle metadata binding mismatch")
    actual_metadata_tid = next(iter(actual_metadata))
    if (post.sm_tid, post.pm_rank0_tid, post.pm_rank1_tid) != tuple(
        node.outs[0] for node in unodes
    ):
        raise ValueError("top-k unshuffle output fact roles mismatch")

    def unique_route(nodes, unode, expected_input, expected_rank):
        matches = [
            (index, node)
            for index, node in enumerate(nodes)
            if unode.ins[0] in node.outs
        ]
        if len(matches) != 1:
            raise ValueError("top-k unshuffle projection lacks one actual writer")
        index, node = matches[0]
        if (
            node.op != "FW_topk_routing"
            or node.rank != expected_rank
            or len(node.ins) != 1
            or node.ins[0] != expected_input
            or len(node.outs) != 3
            or node.outs[projection] != unode.ins[0]
            or not node.params
            or len(node.params) != 2
            or node.params[1] != 1
        ):
            raise ValueError("top-k unshuffle projection writer role mismatch")
        return index, node

    sm_route_pos, rsm = unique_route(sm_nodes, usm, pre.sm_tid, 0)
    pm0_route_pos, rp0 = unique_route(pm_nodes, up0, pre.pm_rank0_tid, 0)
    pm1_route_pos, rp1 = unique_route(pm_nodes, up1, pre.pm_rank1_tid, 1)
    if not (
        sm_route_pos < transition.sm_node_indices[0] - sm_start
        and pm0_route_pos < transition.pm_node_indices[0] - pm_start
        and pm1_route_pos < transition.pm_node_indices[1] - pm_start
        and rsm.params == rp0.params == rp1.params
    ):
        raise ValueError("top-k/unshuffle writers are not exactly source ordered")
    top_k = rsm.params[0]

    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if pre.fact_id not in before.fact_ids or post.fact_id not in after.fact_ids:
        raise ValueError("top-k unshuffle relation is not live")
    if not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("top-k unshuffle state delta mismatch")
    authority = {item.fact_id: item for item in chain.authority_facts}
    live_authority = [authority[item] for item in before.fact_ids if item in authority]

    def authority_one(kind, predicate, label):
        matches = [item for item in live_authority if item.kind == kind and predicate(item)]
        if len(matches) != 1:
            raise ValueError(f"top-k unshuffle lacks unique live {label}: {len(matches)}")
        return matches[0]

    pre_alias = authority_one(
        "tensor_eq",
        lambda item: item.left_side == "pm" and item.left_tid == pre.metadata_tid
        and item.right_side == "pm",
        "input metadata equality",
    )
    node_alias = authority_one(
        "tensor_eq",
        lambda item: (
            item.left_side,
            item.left_tid,
            item.right_side,
            item.right_tid,
        ) == ("pm", actual_metadata_tid, "pm", pre_alias.right_tid),
        "unshuffle metadata equality",
    )
    packed = authority_one(
        "packed_cu",
        lambda item: (
            item.side,
            item.tid,
            item.total_tokens,
            item.num_ranks,
        ) == ("pm", pre_alias.right_tid, pre.full_shape[0], 2),
        "metadata-region PackedCu authority",
    )

    sm_name = f"{segment.segment_id}_sm_nodes"
    pm_name = f"{segment.segment_id}_pm_nodes"
    sm_text = ", ".join(_node_text(item) for item in sm_nodes)
    pm_text = ", ".join(_node_text(item) for item in pm_nodes)
    writer_lines = []
    writer_results = []
    lines = [
        f"private def {sm_name} : List NodeDecl := [{sm_text}]",
        f"private def {pm_name} : List NodeDecl := [{pm_text}]",
        "",
        f"private def {segment.segment_id} :",
        (f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} "
         f"{before.state_id} {after.state_id} where"),
        f"  smNodes := {sm_name}",
        f"  pmNodes := {pm_name}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        (f"    let smFinal := {sm_name}.foldl "
         f"(applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore"),
        (f"    let pmFinal := {pm_name}.foldl "
         f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore"),
        (f"    have hframe : {before.state_id}.Holds smFinal pmFinal := "
         f"{segment.segment_id}_frame smStore pmStore hstate"),
        f"    have hIn : {pre.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        (f"    change GeneratedPatterns.Zigzag2Rel (smFinal {pre.sm_tid}) "
        f"(pmFinal {pre.pm_rank0_tid}) (pmFinal {pre.pm_rank1_tid}) "
        f"(pmFinal {pre.metadata_tid}) {_shape_text(pre.full_shape)} "
        f"{_shape_text(pre.shard_shape)} at hIn"),
        f"    have hPreAlias : {pre_alias.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    have hNodeAlias : {node_alias.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    have hPacked : {packed.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change pmFinal {pre.metadata_tid} = pmFinal {pre_alias.right_tid} at hPreAlias",
        f"    change pmFinal {actual_metadata_tid} = pmFinal {pre_alias.right_tid} at hNodeAlias",
        (f"    change ZigzagCollective.PackedCuSeqlensWF (pmFinal {pre_alias.right_tid}) "
         f"{packed.total_tokens} 2 at hPacked"),
        f"    have hSharedMetadata : pmFinal {pre.metadata_tid} = pmFinal {actual_metadata_tid} :=",
        "      hPreAlias.trans hNodeAlias.symm",
        f"    have hDecodedPre : decodeCuSeqlens (pmFinal {pre.metadata_tid}) = [0, {packed.total_tokens}] := by",
        "      rw [hPreAlias]", "      exact hPacked.decoded_single",
        f"    have hDecodedNode : decodeCuSeqlens (pmFinal {actual_metadata_tid}) = [0, {packed.total_tokens}] := by",
        "      rw [hNodeAlias]", "      exact hPacked.decoded_single",
    ]

    def topk_value(side, absolute_index, node, output_tid, label):
        graph = ir.sm_graph_ref if side == "sm" else ir.pm_graph_ref
        store, final = ("smStore", "smFinal") if side == "sm" else ("pmStore", "pmFinal")
        nodes, nodes_name, base = (
            (sm_nodes, sm_name, sm_start) if side == "sm" else (pm_nodes, pm_name, pm_start)
        )
        params = _shape_text(node.params)
        selector = (".fst", ".snd.fst", ".snd.snd")[projection]
        expression = (
            f"(fw_topk_routing ({{store}} {node.ins[0]}) ({params}.getD 0 1) "
            f"((({{store}} {node.ins[0]}).shape.reverse.head?).getD ({params}.getD 1 1))){selector}"
        )
        apply_lines = [
            "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "  (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "simp [applyNodeDistributed, applyNodeRingAttn]",
            (f"simpa using (applyNode_fw_topk_routing_{lemma_name}_out {graph} t "
             f"{node.rank} {node.ins[0]} {node.outs[0]} {node.outs[1]} "
             f"{node.outs[2]} {params}{lemma_extra})"),
        ]
        writer_results.append((
            label, f"{final} {output_tid} = {expression.format(store=final)}",
        ))
        writer_lines.extend(_render_mixed_final_value(
            name=label, graph=graph, initial_store=store, final_store=final,
            final_equality=("hsm" if side == "sm" else "hpm"),
            nodes_name=nodes_name, nodes=nodes,
            position=absolute_index - base, output_tid=output_tid,
            input_tids=tuple(node.ins), written_tids=set(),
            expression=expression, apply_lines=apply_lines,
        ))

    topk_value("sm", sm_start + sm_route_pos, rsm, usm.ins[0], "hRouteSmValue")
    topk_value("pm", pm_start + pm0_route_pos, rp0, up0.ins[0], "hRoutePm0Value")
    topk_value("pm", pm_start + pm1_route_pos, rp1, up1.ins[0], "hRoutePm1Value")
    semantic_insert = len(lines)
    lines.extend([
        "    have hRouteSm := hRouteSmValue",
        "    rw [hIn.full_shape] at hRouteSm",
        "    simp at hRouteSm",
        "    have hRoutePm0 := hRoutePm0Value",
        "    rw [hIn.rank0_shape] at hRoutePm0",
        "    simp at hRoutePm0",
        "    have hRoutePm1 := hRoutePm1Value",
        "    rw [hIn.rank1_shape] at hRoutePm1",
        "    simp at hRoutePm1",
        (f"    have hProjected := GeneratedPatterns.Zigzag2Rel.{theorem_name} "
         f"{rows} {num_experts} {top_k} hIn (by decide) (by decide) "
         "(by decide) hDecodedPre"),
        (f"    have hUnshuffleInput : GeneratedPatterns.Zigzag2Rel "
         f"(smFinal {usm.ins[0]}) (pmFinal {up0.ins[0]}) (pmFinal {up1.ins[0]}) "
         f"(pmFinal {pre.metadata_tid}) {_shape_text(post.full_shape)} "
         f"{_shape_text(post.shard_shape)} := by"),
        "      rw [hRouteSm, hRoutePm0, hRoutePm1]",
        "      exact hProjected",
        "    rw [hSharedMetadata] at hUnshuffleInput",
    ])

    def unshuffle_value(side, absolute_index, node, peers, label):
        graph = ir.sm_graph_ref if side == "sm" else ir.pm_graph_ref
        store, final = ("smStore", "smFinal") if side == "sm" else ("pmStore", "pmFinal")
        nodes, nodes_name, base = (
            (sm_nodes, sm_name, sm_start) if side == "sm" else (pm_nodes, pm_name, pm_start)
        )
        values = ", ".join(f"{{store}} {peer.ins[0]}" for peer in peers)
        expression = (
            f"ZigzagCollective.fw_maybe_unshuffle_collective [{values}] "
            f"(decodeCuSeqlens ({{store}} {actual_metadata_tid})) "
            f"{node.params[0]} {node.params[1]}"
        )
        apply_lines = [
            "rw [applyNodeDistributedFaithful_unshuffle_out]",
            "unfold applyNodeFaithfulUnshuffleValue",
            (f"rw [show {graph}.replicaBuddies {_node_text(node)} = "
             f"[{', '.join(_node_text(peer) for peer in peers)}] by native_decide]"),
            "rfl",
        ]
        semantic_inputs = tuple(peer.ins[0] for peer in peers) + (actual_metadata_tid,)
        writer_results.append((
            label, f"{final} {node.outs[0]} = {expression.format(store=final)}",
        ))
        writer_lines.extend(_render_mixed_final_value(
            name=label, graph=graph, initial_store=store, final_store=final,
            final_equality=("hsm" if side == "sm" else "hpm"),
            nodes_name=nodes_name, nodes=nodes,
            position=absolute_index - base, output_tid=node.outs[0],
            input_tids=semantic_inputs, written_tids=set(),
            expression=expression, apply_lines=apply_lines,
        ))

    unshuffle_value("sm", transition.sm_node_indices[0], usm, (usm,), "hUnshuffleSm")
    unshuffle_value("pm", transition.pm_node_indices[0], up0, (up0, up1), "hUnshufflePm0")
    unshuffle_value("pm", transition.pm_node_indices[1], up1, (up0, up1), "hUnshufflePm1")
    writer_theorem = f"{segment.segment_id}_writer_values"
    helper = [
        f"private theorem {writer_theorem} (smStore pmStore smFinal pmFinal : Store)",
        (f"    (hsm : smFinal = {sm_name}.foldl "
         f"(applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore)"),
        (f"    (hpm : pmFinal = {pm_name}.foldl "
         f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) :"),
        "    " + " ∧\n    ".join(result for _name, result in writer_results) + " := by",
        f"    let smNodes : List NodeDecl := {sm_name}",
        f"    let pmNodes : List NodeDecl := {pm_name}",
        *writer_lines,
        "    exact ⟨" + ", ".join(name for name, _result in writer_results) + "⟩",
        "",
    ]
    frame_theorem = f"{segment.segment_id}_frame"
    frame_helper = [
        f"private theorem {frame_theorem} (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        (f"    {before.state_id}.Holds "
         f"({sm_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore) "
         f"({pm_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) := by"),
        f"    let smNodes : List NodeDecl := {sm_name}",
        f"    let pmNodes : List NodeDecl := {pm_name}",
        "    apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "    · native_decide", "    · native_decide",
        "    · simp only [smNodes]", "      native_decide",
        "    · simp only [pmNodes]", "      native_decide",
        "",
    ]
    writer_call = [
        (f"    have hWriterValues := {writer_theorem} smStore pmStore smFinal pmFinal "
         "(by rfl) (by rfl)"),
    ]
    for index, (name, _result) in enumerate(writer_results):
        projection_text = ".2" * index + (
            ".1" if index < len(writer_results) - 1 else ""
        )
        writer_call.append(f"    have {name} := hWriterValues{projection_text}")
    lines[semantic_insert:semantic_insert] = writer_call
    tail = _shape_text(post.shard_shape[1:])
    lines.extend([
        f"    have hUnshuffleCore : smFinal {usm.ins[0]} = allGatherPrimDimN 0 2 0",
        (f"        [ZigzagCollective.fw_maybe_unshuffle_collective "
         f"[pmFinal {up0.ins[0]}, pmFinal {up1.ins[0]}] "
         f"(decodeCuSeqlens (pmFinal {actual_metadata_tid})) 2 0,"),
        (f"         ZigzagCollective.fw_maybe_unshuffle_collective "
         f"[pmFinal {up0.ins[0]}, pmFinal {up1.ins[0]}] "
         f"(decodeCuSeqlens (pmFinal {actual_metadata_tid})) 2 1] := by"),
        (f"      exact GeneratedPatterns.Zigzag2Rel.unshuffle_gather_single "
         f"{rows} {tail} hUnshuffleInput"),
        "        (by decide) (by decide) rfl hDecodedNode",
        f"    have hOut : {post.fact_id}.Holds smFinal pmFinal := by",
        (f"      change GeneratedPatterns.Ordinary2Rel (smFinal {post.sm_tid}) "
         f"(pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) "
         f"{_shape_text(post.full_shape)} {_shape_text(post.shard_shape)}"),
        "      refine { full_value := ?_, full_shape := ?_, rank0_shape := ?_, rank1_shape := ?_ }",
        "      · rw [hUnshuffleSm, hUnshufflePm0, hUnshufflePm1]",
        "        simp only [ZigzagCollective.fw_maybe_unshuffle_collective_cpSize_one, List.getD_cons_zero]",
        "        exact hUnshuffleCore",
        "      · rw [hUnshuffleSm]",
        "        simp only [ZigzagCollective.fw_maybe_unshuffle_collective_cpSize_one, List.getD_cons_zero]",
        "        exact hUnshuffleInput.full_shape",
        "      · rw [hUnshufflePm0, ZigzagCollective.fw_maybe_unshuffle_collective_shape]",
        "        simp only [List.getD_cons_zero]",
        "        exact hUnshuffleInput.rank0_shape",
        "      · rw [hUnshufflePm1, ZigzagCollective.fw_maybe_unshuffle_collective_shape]",
        "        simp only [List.getD_cons_succ, List.getD_cons_zero]",
        "        exact hUnshuffleInput.rank1_shape",
        "    exact RelationState.Holds.mono_insert hframe hOut (by native_decide)",
        "",
    ])
    semantic_start = next(
        index for index, line in enumerate(lines)
        if line.startswith("    have hIn :")
    )
    semantic_end = next(
        index for index, line in enumerate(lines)
        if line.startswith("    exact RelationState.Holds.mono_insert")
    )
    semantic_body = lines[semantic_start:semantic_end]
    for call_line in writer_call:
        if call_line not in semantic_body:
            raise ValueError("top-k unshuffle writer call escaped semantic block")
        semantic_body.remove(call_line)
    relation_theorem = f"{segment.segment_id}_relation"
    semantic_helper = [
        f"private theorem {relation_theorem} (smFinal pmFinal : Store)",
        f"    (hframe : {before.state_id}.Holds smFinal pmFinal)",
    ]
    semantic_helper.extend(
        f"    ({name} : {result})" for name, result in writer_results
    )
    semantic_helper.extend([
        f"    : {post.fact_id}.Holds smFinal pmFinal := by",
        *semantic_body,
        "    exact hOut",
        "",
    ])
    relation_call = (
        f"    have hOut := {relation_theorem} smFinal pmFinal hframe "
        + " ".join(name for name, _result in writer_results)
    )
    lines[semantic_start:semantic_end + 1] = [
        *writer_call,
        relation_call,
        "    exact RelationState.Holds.mono_insert hframe hOut (by native_decide)",
    ]
    return "\n".join(
        lines[:3] + helper + frame_helper + semantic_helper + lines[3:]
    )

def render_closed_norm_full_producer_segment(ir: GoalIR, relation, segment_id: str) -> str:
    """Render one standalone two-rank norm-linear full-producer component."""
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("norm full-producer renderer requires a complete closed chain")
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("norm full-producer segment must own one transition")
    transition = {item.transition_id: item for item in relation.transition_specs}[
        segment.transition_ids[0]
    ]
    expected_rule = "FW_norm_linear-full-producer-chunks-zigzag-two-rank"
    expected_theorem = (
        "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel."
        "norm_linear_fullProducer_chunks"
    )
    if transition.rule_id != expected_rule or transition.lean_theorem != expected_theorem:
        raise ValueError("segment is not the registered zigzag norm full-producer family")
    if len(transition.pre_facts) != 1 or len(transition.post_facts) != 1:
        raise ValueError("norm full-producer transition must have one pre/post fact")

    records = {item.source: item for item in chain.relation_facts}
    pre = records[transition.pre_facts[0]]
    post = records[transition.post_facts[0]]
    if (
        pre.kind != "zigzag"
        or post.kind != "zigzag"
        or pre.metadata_tid is None
        or (pre.metadata_tid, pre.metadata_region_id)
        != (post.metadata_tid, post.metadata_region_id)
        or len(pre.shard_shape) != 2
        or len(post.shard_shape) != 2
        or pre.full_shape != (2 * pre.shard_shape[0], pre.shard_shape[1])
        or post.full_shape != (2 * post.shard_shape[0], post.shard_shape[1])
        or pre.shard_shape[0] != post.shard_shape[0]
    ):
        raise ValueError("norm full-producer relation payload mismatch")

    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    sm_start, pm_start = segment.sm_range[0], segment.pm_range[0]
    if len(transition.sm_node_indices) != 2 or len(transition.pm_node_indices) != 5:
        raise ValueError("norm full-producer semantic footprint mismatch")
    sm_float_i, sm_norm_i = transition.sm_node_indices
    gather_i, pm_float_i, producer_i, chunk0_i, chunk1_i = transition.pm_node_indices
    sm_float, sm_norm = (ir.sm_nodes[index] for index in (sm_float_i, sm_norm_i))
    gather, pm_float, producer, chunk0, chunk1 = (
        ir.pm_nodes[index]
        for index in (gather_i, pm_float_i, producer_i, chunk0_i, chunk1_i)
    )
    sm_float_pos, sm_norm_pos = sm_float_i - sm_start, sm_norm_i - sm_start
    gather_pos, pm_float_pos, producer_pos, chunk0_pos, chunk1_pos = (
        index - pm_start
        for index in (gather_i, pm_float_i, producer_i, chunk0_i, chunk1_i)
    )
    if not (
        0 <= sm_float_pos < sm_norm_pos < len(sm_nodes)
        and 0 <= gather_pos < pm_float_pos < producer_pos < chunk0_pos < chunk1_pos
        < len(pm_nodes)
    ):
        raise ValueError("norm full-producer semantic nodes are not source ordered")
    if (
        sm_nodes[sm_float_pos] != sm_float
        or sm_nodes[sm_norm_pos] != sm_norm
        or pm_nodes[gather_pos] != gather
        or pm_nodes[pm_float_pos] != pm_float
        or pm_nodes[producer_pos] != producer
        or pm_nodes[chunk0_pos] != chunk0
        or pm_nodes[chunk1_pos] != chunk1
    ):
        raise ValueError("norm full-producer nodes lie outside the exact component slice")
    weight_tid = sm_norm.ins[1]
    if (
        (sm_float.op, sm_float.rank, sm_float.ins, sm_float.params)
        != ("FW_float", 0, [pre.sm_tid], None)
        or len(sm_float.outs) != 1
        or (sm_norm.op, sm_norm.rank, sm_norm.ins, sm_norm.params)
        != ("FW_norm_linear", 0, [sm_float.outs[0], weight_tid], None)
        or sm_norm.outs != [post.sm_tid]
        or (gather.op, gather.rank, gather.ins, gather.params)
        != ("AllGatherPrim", 0, [pre.pm_rank0_tid, pre.pm_rank1_tid], [0])
        or len(gather.outs) != 1
        or (pm_float.op, pm_float.rank, pm_float.ins, pm_float.outs, pm_float.params)
        != ("FW_float", 1, gather.outs, sm_float.outs, None)
        or (producer.op, producer.rank, producer.ins, producer.outs, producer.params)
        != ("FW_norm_linear", 1, [pm_float.outs[0], weight_tid], sm_norm.outs, None)
        or (chunk0.op, chunk0.rank, chunk0.ins, chunk0.outs, chunk0.params)
        != ("ChunkPrim", 0, producer.outs, [post.pm_rank0_tid], [0])
        or (chunk1.op, chunk1.rank, chunk1.ins, chunk1.outs, chunk1.params)
        != ("ChunkPrim", 1, producer.outs, [post.pm_rank1_tid], [0])
    ):
        raise ValueError("norm full-producer node roles mismatch")
    if any(post.sm_tid in node.outs for node in sm_nodes[sm_norm_pos + 1 :]):
        raise ValueError("norm SM output is not final in the component")
    if any(
        tid in node.outs
        for tid in (post.pm_rank0_tid, post.pm_rank1_tid)
        for node in pm_nodes[chunk1_pos + 1 :]
    ):
        raise ValueError("norm PM chunk output is not final in the component")

    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if pre.fact_id not in before.fact_ids or post.fact_id not in after.fact_ids:
        raise ValueError("norm full-producer pre/post fact is not live")
    if not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("norm full-producer post-state introduces an unproved fact")
    authority = {item.fact_id: item for item in chain.authority_facts}
    live_authority = [authority[item] for item in before.fact_ids if item in authority]

    def unique_authority(kind: str, predicate, label: str):
        matches = [item for item in live_authority if item.kind == kind and predicate(item)]
        if len(matches) != 1:
            raise ValueError(f"norm full-producer lacks unique live {label}: {len(matches)}")
        return matches[0]

    weight_shape = (post.shard_shape[1], pre.shard_shape[1])
    weight_eq = unique_authority(
        "tensor_eq",
        lambda item: (
            item.left_side,
            item.left_tid,
            item.right_side,
            item.right_tid,
        )
        == ("sm", weight_tid, "pm", weight_tid),
        f"weight equality {weight_tid}",
    )
    weight_shape_fact = unique_authority(
        "tensor_shape",
        lambda item: (item.side, item.tid, item.shape)
        == ("pm", weight_tid, weight_shape),
        f"weight shape {weight_tid}",
    )
    metadata_eq = unique_authority(
        "tensor_eq",
        lambda item: (item.left_side, item.left_tid, item.right_side)
        == ("pm", pre.metadata_tid, "pm"),
        f"metadata equality {pre.metadata_tid}",
    )
    packed = unique_authority(
        "packed_cu",
        lambda item: (
            item.side,
            item.tid,
            item.total_tokens,
            item.num_ranks,
        )
        == ("pm", metadata_eq.right_tid, pre.full_shape[0], 2),
        f"packed metadata {metadata_eq.right_tid}",
    )

    sm_name = f"{segment.segment_id}_sm_nodes"
    pm_name = f"{segment.segment_id}_pm_nodes"
    sm_text = ", ".join(_node_text(item) for item in sm_nodes)
    pm_text = ", ".join(_node_text(item) for item in pm_nodes)
    lines = [
        f"private def {sm_name} : List NodeDecl := [{sm_text}]",
        f"private def {pm_name} : List NodeDecl := [{pm_text}]",
        "",
        f"private def {segment.segment_id} :",
        (f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} "
        f"{before.state_id} {after.state_id} where"),
        f"  smNodes := {sm_name}",
        f"  pmNodes := {pm_name}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := {sm_name}",
        f"    let pmNodes : List NodeDecl := {pm_name}",
        (f"    let smFinal := {sm_name}.foldl "
        f"(applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore"),
        (f"    let pmFinal := {pm_name}.foldl "
        f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore"),
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide",
        "      · native_decide",
        "      · native_decide",
        "      · native_decide",
        f"    have hNormIn : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hWeightEq : {weight_eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hWeightShape : {weight_shape_fact.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    change smStore {weight_tid} = pmStore {weight_tid} at hWeightEq",
        f"    change (pmStore {weight_tid}).shape = {_shape_text(list(weight_shape))} at hWeightShape",
        f"    have hMetadataEq : pmStore {pre.metadata_tid} = pmStore {metadata_eq.right_tid} := by",
        (f"      simpa [{metadata_eq.fact_id}, RelationFact.Holds, StoreSide.read] using "
        f"(hstate _ (by native_decide : {metadata_eq.fact_id} ∈ {before.state_id}.facts))"),
        (f"    have hPackedCu : ZigzagCollective.PackedCuSeqlensWF "
        f"(pmStore {metadata_eq.right_tid}) {packed.total_tokens} 2 := by"),
        (f"      simpa [{packed.fact_id}, RelationFact.Holds, StoreSide.read] using "
        f"(hstate _ (by native_decide : {packed.fact_id} ∈ {before.state_id}.facts))"),
        (f"    have hDecodedCu : decodeCuSeqlens (pmStore {pre.metadata_tid}) = "
        f"[0, {packed.total_tokens}] := by"),
        "      rw [hMetadataEq]",
        "      exact hPackedCu.decoded_single",
        (f"    let smBeforeNorm := (smNodes.take {sm_norm_pos}).foldl "
        f"(applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore"),
        f"    have hSmFloat : smBeforeNorm {sm_float.outs[0]} = smStore {sm_float.ins[0]} := by",
        (f"      change ((smNodes.take {sm_norm_pos}).foldl "
        f"(applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore) {sm_float.outs[0]} = _"),
        (f"      rw [show smNodes.take {sm_norm_pos} = "
        f"(smNodes.take {sm_norm_pos}).take {sm_float_pos} ++ [{_node_text(sm_float)}] ++ "
        f"(smNodes.take {sm_norm_pos}).drop {sm_float_pos + 1} by native_decide]"),
        f"      exact foldl_faithful_unary_middle_writer {ir.sm_graph_ref} smStore",
        (f"        ((smNodes.take {sm_norm_pos}).take {sm_float_pos}) "
        f"((smNodes.take {sm_norm_pos}).drop {sm_float_pos + 1}) {_node_text(sm_float)}"),
        f"        {sm_float.ins[0]} {sm_float.outs[0]} (fun x => x) (by",
        "          intro t",
        "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
        "          simp [applyNodeDistributed, applyNodeRingAttn]",
        (f"          exact applyNode_fw_float_out {ir.sm_graph_ref} t {sm_float.rank} "
        f"{sm_float.ins[0]} {sm_float.outs[0]} [])"),
        "        (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
        f"    have hSmWeight : smBeforeNorm {weight_tid} = smStore {weight_tid} := by",
        (f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.sm_graph_ref} "
        f"(smNodes.take {sm_norm_pos}) smStore {weight_tid} (by native_decide) (by native_decide)"),
        (f"    have hSmNorm : smFinal {sm_norm.outs[0]} = "
        f"fw_norm_linear (smStore {sm_float.ins[0]}) (smStore {weight_tid}) := by"),
        (f"      change (smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore) "
        f"{sm_norm.outs[0]} = _"),
        (f"      rw [show smNodes = smNodes.take {sm_norm_pos} ++ [{_node_text(sm_norm)}] ++ "
        f"smNodes.drop {sm_norm_pos + 1} by native_decide]"),
        "      calc",
        f"        _ = fw_norm_linear (smBeforeNorm {sm_norm.ins[0]}) (smBeforeNorm {weight_tid}) := by",
        (f"          exact foldl_faithful_binary_writer {ir.sm_graph_ref} smStore "
        f"(smNodes.take {sm_norm_pos}) (smNodes.drop {sm_norm_pos + 1}) {_node_text(sm_norm)}"),
        (f"            {sm_norm.ins[0]} {weight_tid} {sm_norm.outs[0]} "
        f"(fun x w => fw_norm_linear x w) (by"),
        "              intro t",
        "              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "                (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
        "              simp [applyNodeDistributed, applyNodeRingAttn]",
        (f"              exact applyNode_fw_norm_linear_out {ir.sm_graph_ref} t {sm_norm.rank} "
        f"{sm_norm.ins[0]} {weight_tid} {sm_norm.outs[0]} [])"),
        "            (by native_decide) (by native_decide)",
        "        _ = _ := by rw [hSmFloat, hSmWeight]",
        (f"    let pmBeforeFloat := (pmNodes.take {pm_float_pos}).foldl "
        f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore"),
        (f"    have hGather : pmBeforeFloat {gather.outs[0]} = allGatherPrimDimN 0 2 0 "
        f"[pmStore {gather.ins[0]}, pmStore {gather.ins[1]}] := by"),
        (f"      change ((pmNodes.take {pm_float_pos}).foldl "
        f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {gather.outs[0]} = _"),
        (f"      rw [show pmNodes.take {pm_float_pos} = "
        f"(pmNodes.take {pm_float_pos}).take {gather_pos} ++ [{_node_text(gather)}] ++ "
        f"(pmNodes.take {pm_float_pos}).drop {gather_pos + 1} by native_decide]"),
        f"      exact foldl_faithful_binary_middle_writer {ir.pm_graph_ref} pmStore",
        (f"        ((pmNodes.take {pm_float_pos}).take {gather_pos}) "
        f"((pmNodes.take {pm_float_pos}).drop {gather_pos + 1}) {_node_text(gather)}"),
        (f"        {gather.ins[0]} {gather.ins[1]} {gather.outs[0]} "
        "(fun x y => allGatherPrimDimN 0 2 0 [x, y]) (by"),
        "          intro t",
        "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
        "          simp [applyNodeDistributed, applyNodeRingAttn]",
        (f"          rw [applyNode_allGatherPrimDimN_out {ir.pm_graph_ref} t 0 "
        f"[{gather.ins[0]}, {gather.ins[1]}] {gather.outs[0]} 0]"),
        f"          rw [show {ir.pm_graph_ref}.numRanks = 2 by rfl]",
        "          rfl) (by native_decide) (by native_decide) (by native_decide)",
        "        (by native_decide) (by native_decide)",
        (f"    let pmBeforeProducer := (pmNodes.take {producer_pos}).foldl "
        f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore"),
        (f"    have hPmFloat : pmBeforeProducer {pm_float.outs[0]} = "
        f"allGatherPrimDimN 0 2 0 [pmStore {gather.ins[0]}, pmStore {gather.ins[1]}] := by"),
        (f"      rw [show pmBeforeProducer {pm_float.outs[0]} = "
        f"(fun x _ => x) (pmBeforeFloat {pm_float.ins[0]}) "
        f"(pmBeforeFloat {pm_float.ins[0]}) by"),
        (f"        change ((pmNodes.take {producer_pos}).foldl "
        f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {pm_float.outs[0]} = _"),
        (f"        rw [show pmNodes.take {producer_pos} = pmNodes.take {pm_float_pos} ++ "
        f"[{_node_text(pm_float)}] ++ (pmNodes.take {producer_pos}).drop {pm_float_pos + 1} "
        "by native_decide]"),
        (f"        exact foldl_faithful_binary_writer {ir.pm_graph_ref} pmStore "
        f"(pmNodes.take {pm_float_pos}) ((pmNodes.take {producer_pos}).drop {pm_float_pos + 1}) "
        f"{_node_text(pm_float)} {pm_float.ins[0]} {pm_float.ins[0]} {pm_float.outs[0]} "
        "(fun x _ => x) (by"),
        "          intro t",
        "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
        "          simp [applyNodeDistributed, applyNodeRingAttn]",
        (f"          exact applyNode_fw_float_out {ir.pm_graph_ref} t {pm_float.rank} "
        f"{pm_float.ins[0]} {pm_float.outs[0]} [])"),
        "          (by native_decide) (by native_decide)]",
        "      exact hGather",
        f"    have hPmWeight : pmBeforeProducer {weight_tid} = pmStore {weight_tid} := by",
        (f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} "
        f"(pmNodes.take {producer_pos}) pmStore {weight_tid} (by native_decide) (by native_decide)"),
    ]
    for rank, (chunk, chunk_pos) in enumerate(((chunk0, chunk0_pos), (chunk1, chunk1_pos))):
        lines += [
            (f"    let pmBeforeChunk{rank} := (pmNodes.take {chunk_pos}).foldl "
            f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore"),
            (f"    have hProducer{rank} : pmBeforeChunk{rank} {producer.outs[0]} = "
            f"fw_norm_linear (allGatherPrimDimN 0 2 0 "
            f"[pmStore {gather.ins[0]}, pmStore {gather.ins[1]}]) (pmStore {weight_tid}) := by"),
            (f"      rw [show pmBeforeChunk{rank} {producer.outs[0]} = "
            f"fw_norm_linear (pmBeforeProducer {producer.ins[0]}) "
            f"(pmBeforeProducer {producer.ins[1]}) by"),
            (f"        change ((pmNodes.take {chunk_pos}).foldl "
            f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {producer.outs[0]} = _"),
            (f"        rw [show pmNodes.take {chunk_pos} = pmNodes.take {producer_pos} ++ "
            f"[{_node_text(producer)}] ++ (pmNodes.take {chunk_pos}).drop {producer_pos + 1} "
            "by native_decide]"),
            (f"        exact foldl_faithful_binary_writer {ir.pm_graph_ref} pmStore "
            f"(pmNodes.take {producer_pos}) ((pmNodes.take {chunk_pos}).drop {producer_pos + 1}) "
            f"{_node_text(producer)} {producer.ins[0]} {producer.ins[1]} {producer.outs[0]} "
            "(fun x w => fw_norm_linear x w) (by"),
            "          intro t",
            "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "          simp [applyNodeDistributed, applyNodeRingAttn]",
            (f"          exact applyNode_fw_norm_linear_out {ir.pm_graph_ref} t {producer.rank} "
            f"{producer.ins[0]} {producer.ins[1]} {producer.outs[0]} [])"),
            "          (by native_decide) (by native_decide)]",
            "      rw [hPmFloat, hPmWeight]",
            (f"    have hChunk{rank} : pmFinal {chunk.outs[0]} = chunkPrimDimN 0 2 {rank} "
            f"(pmBeforeChunk{rank} {producer.outs[0]}) := by"),
            (f"      change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) "
            f"{chunk.outs[0]} = _"),
            (f"      rw [show pmNodes = pmNodes.take {chunk_pos} ++ [{_node_text(chunk)}] ++ "
            f"pmNodes.drop {chunk_pos + 1} by native_decide]"),
            (f"      exact foldl_faithful_chunk_writer {ir.pm_graph_ref} pmStore "
            f"(pmNodes.take {chunk_pos}) (pmNodes.drop {chunk_pos + 1}) {rank} "
            f"{producer.outs[0]} {chunk.outs[0]} 0 rfl (by native_decide) (by native_decide)"),
        ]
    lines += [
        f"    have hMetadataFinal : pmFinal {pre.metadata_tid} = pmStore {pre.metadata_tid} := by",
        (f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} "
        f"pmNodes pmStore {pre.metadata_tid} (by native_decide) (by native_decide)"),
        f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
        (f"      change GeneratedPatterns.Zigzag2Rel (smFinal {post.sm_tid}) "
        f"(pmFinal {post.pm_rank0_tid}) (pmFinal {post.pm_rank1_tid}) "
        f"(pmFinal {post.metadata_tid}) {_shape_text(list(post.full_shape))} "
        f"{_shape_text(list(post.shard_shape))}"),
        (f"      change GeneratedPatterns.Zigzag2Rel (smStore {pre.sm_tid}) "
        f"(pmStore {pre.pm_rank0_tid}) (pmStore {pre.pm_rank1_tid}) "
        f"(pmStore {pre.metadata_tid}) {_shape_text(list(pre.full_shape))} "
        f"{_shape_text(list(pre.shard_shape))} at hNormIn"),
        "      rw [hMetadataFinal]",
        (f"      exact GeneratedPatterns.Zigzag2Rel.norm_linear_fullProducer_chunks "
        f"{pre.shard_shape[0]} {pre.shard_shape[1]} {post.shard_shape[1]}"),
        "        hNormIn hWeightShape hWeightEq hSmNorm hGather hProducer0 hChunk0",
        (f"        (calc pmFinal {chunk1.outs[0]} = chunkPrimDimN 0 2 1 "
        f"(pmBeforeChunk1 {producer.outs[0]}) := hChunk1"),
        (f"          _ = chunkPrimDimN 0 2 1 (pmBeforeChunk0 {producer.outs[0]}) := "
        "congrArg (chunkPrimDimN 0 2 1) (hProducer1.trans hProducer0.symm))"),
        "        (by decide) (by decide) (by decide) (by decide) hDecodedCu",
        "    exact RelationState.Holds.mono_insert hframe hout (by native_decide)",
        "",
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
    if family == ("zigzag-to-ordinary-unshuffle-two-rank",):
        return render_closed_unshuffle_segment(ir, relation, segment_id)
    if family == ("zigzag-topk-unshuffle-two-rank",):
        return render_closed_topk_unshuffle_segment(ir, relation, segment_id)
    if family == ("FW_norm_linear-full-producer-chunks-zigzag-two-rank",):
        return render_closed_norm_full_producer_segment(ir, relation, segment_id)
    if family == ("inner-chunk-ce-projection-gather-two-rank",):
        ce_certificates = [
            certificate for certificate in relation.certificates
            if getattr(certificate, "rule_id", None)
            == "inner-chunk-ce-projection-gather-two-rank"
        ]
        if len(ce_certificates) != 1:
            raise ValueError("closed CE segment lacks one exact certificate")
        projection = ce_certificates[0].output_projection
        if projection == ".fst":
            return render_closed_ce_fst_segment(ir, relation, segment_id)
        if projection == ".snd":
            return render_closed_ce_snd_segment(ir, relation, segment_id)
        raise ValueError(f"unsupported closed CE projection: {projection!r}")
    if family == ("indexed-stack-gather-two-rank",):
        return render_closed_indexed_stack_segment(ir, relation, segment_id)
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
        family
        and family[0] == "FW_per_head_mix_precision_linear-full-producer-chunks-zigzag-two-rank"
        and all(item == "to-ordinary-two-rank" for item in family[1:])
    ):
        return render_closed_full_producer_to_segment(ir, relation, segment_id)
    semantic_family = tuple(
        item for item in family
        if item not in (
            "ordinary-topk-projection-two-rank",
            "zigzag-topk-unshuffle-two-rank",
        )
    )
    if (
        len(semantic_family) == 16
        and len(family) - len(semantic_family) <= 1
        and semantic_family[0] in (
            "FW_norm_linear-full-producer-chunks-ordinary-two-rank",
            "FW_norm_linear-full-producer-chunks-zigzag-two-rank",
        )
    ):
        return render_closed_mixed_moe_segment(ir, relation, segment_id)
    raise ValueError(f"unsupported closed segment family {family!r} at {segment_id}")



def _lean_shape_tuple(shape) -> str:
    return "[" + ", ".join(str(int(value)) for value in shape) + "]"


def _validate_closed_namespace(namespace: str) -> None:
    if not namespace or not namespace.replace("_", "").isalnum():
        raise ValueError(f"invalid closed chain namespace: {namespace!r}")


def _closed_input_class_index(classes, left_tid: int, right_tid: int) -> int | None:
    for index, value_class in enumerate(classes):
        tids = {int(tid) for tid in value_class.tids}
        if left_tid in tids and right_tid in tids:
            return index
    return None


def _external_contract_arguments(ir: GoalIR) -> tuple[str, str, tuple[str, ...]]:
    if not ir.init_goals_ref:
        raise ValueError("external initial-state renderer lacks exact init-goals reference")
    generated_ns = "TrainVerify.Denote.Generated"
    arguments = [
        "    (initSM initPM : Store)",
        f"    (hSM : StoreShapesHold initSM {ir.sm_graph_ref}InitEnv)",
        f"    (hPM : StoreShapesHold initPM {ir.pm_graph_ref}InitEnv)",
        (f"    (hInit : InitGoalsHold {ir.pm_graph_ref}.numRanks "
         f"{ir.init_goals_ref} initSM initPM)"),
        (f"    (hSMValues : InputValueClassesHold "
         f"{generated_ns}.smInputValueClasses initSM)"),
        (f"    (hPMValues : InputValueClassesHold "
         f"{generated_ns}.pmInputValueClasses initPM)"),
    ]
    names = ["initSM", "initPM", "hSM", "hPM", "hInit", "hSMValues", "hPMValues"]
    contract_names = ["hSMValues", "hPMValues"]
    for index, contract in enumerate(ir.packed_cu_contracts):
        if contract.side not in {"sm", "pm"}:
            raise ValueError(f"unsupported packed-CU contract side: {contract.side!r}")
        store = "initSM" if contract.side == "sm" else "initPM"
        name = f"hPacked_{index}"
        arguments.append(
            f"    ({name} : ZigzagCollective.PackedCuSeqlensWF "
            f"({store} {contract.tid}) {contract.total_tokens} {contract.num_ranks})"
        )
        names.append(name)
        contract_names.append(name)
    for index, contract in enumerate(ir.tensor_value_bound_contracts):
        if contract.side not in {"sm", "pm"}:
            raise ValueError(f"unsupported tensor-bound contract side: {contract.side!r}")
        store = "initSM" if contract.side == "sm" else "initPM"
        name = f"hBound_{index}"
        arguments.append(
            f"    ({name} : ∀ l < {contract.length}, "
            f"scalarToNat (valAt ({store} {contract.tid}) l) < {contract.upper_bound})"
        )
        names.append(name)
        contract_names.append(name)
    return "\n".join(arguments), " ".join(names), tuple(contract_names)


def render_closed_external_initial_state(ir: GoalIR, relation, namespace: str) -> str:
    """Derive the exact closed initial state from public external contracts."""
    _validate_closed_namespace(namespace)
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete or not chain.states or not chain.segments:
        raise ValueError("external initial state requires a complete closed chain")
    states = {state.state_id: state for state in chain.states}
    initial = states.get(chain.segments[0].pre_state_id)
    if initial is None:
        raise ValueError("closed chain initial state is missing")
    authority = {fact.fact_id: fact for fact in chain.authority_facts}
    authority[chain.anchor_fact.fact_id] = chain.anchor_fact
    missing = [fact_id for fact_id in initial.fact_ids if fact_id not in authority]
    if missing:
        raise ValueError(f"closed public initial state contains non-authority facts: {missing!r}")

    common_args, call_args, _ = _external_contract_arguments(ir)
    generated_ns = "TrainVerify.Denote.Generated"
    helpers: dict[str, str] = {}
    blocks: list[str] = []
    for fact_id in initial.fact_ids:
        fact = authority[fact_id]
        helper = f"{namespace}_{fact_id}_from_external_inputs"
        helpers[fact_id] = helper
        body = [
            f"private theorem {helper}",
            common_args,
            f"    : {fact_id}.Holds initSM initPM := by",
            f"  unfold {fact_id} RelationFact.Holds StoreSide.read",
        ]
        if fact.kind == "tensor_shape":
            if fact.side not in {"sm", "pm"}:
                raise ValueError(f"unsupported tensor shape side in {fact_id}: {fact.side!r}")
            hypothesis = "hSM" if fact.side == "sm" else "hPM"
            body.append(
                f"  exact {hypothesis} {fact.tid} {_lean_shape_tuple(fact.shape)} "
                "(by native_decide)"
            )
        elif fact.kind == "tensor_eq":
            if fact.left_side == fact.right_side and fact.left_tid == fact.right_tid:
                body.append("  rfl")
            elif fact.left_side == fact.right_side and fact.left_side in {"sm", "pm"}:
                classes = (
                    ir.sm_input_value_classes if fact.left_side == "sm"
                    else ir.pm_input_value_classes
                )
                class_index = _closed_input_class_index(
                    classes, fact.left_tid, fact.right_tid
                )
                if class_index is None:
                    raise ValueError(
                        f"tensor equality {fact_id} lacks an exact input-value class"
                    )
                hypothesis = "hSMValues" if fact.left_side == "sm" else "hPMValues"
                class_name = (
                    "smInputValueClasses" if fact.left_side == "sm"
                    else "pmInputValueClasses"
                )
                body.extend([
                    f"  exact InputValueClassesHold.eq_of_mem {hypothesis}",
                    f"    (c := {generated_ns}.{class_name}[{class_index}]'(by native_decide))",
                    "    (by native_decide) (by native_decide) (by native_decide)",
                ])
            elif fact.left_side == "sm" and fact.right_side == "pm":
                lineage = ir.init_lineages.get(int(fact.left_tid))
                expected_piece = [(0, int(fact.right_tid))]
                if (
                    lineage is None
                    or int(lineage.ts) != int(fact.left_tid)
                    or lineage.tps != expected_piece
                    or int(fact.left_tid) not in ir.full_init_goal_ids
                ):
                    raise ValueError(
                        f"cross-store equality {fact_id} is not an exact singleton init lineage"
                    )
                goal = f"{generated_ns}.initGoal_{fact.left_tid}"
                body.extend([
                    f"  have hi := hInit {goal} (by native_decide)",
                    f"  exact InitGoalHolds.singleton_value_eq {ir.pm_graph_ref}.numRanks {goal} initSM initPM",
                    f"    {{ rank := 0, tid := {fact.right_tid} }} hi rfl",
                ])
            else:
                raise ValueError(
                    f"unsupported tensor equality orientation in {fact_id}"
                )
        elif fact.kind == "gather":
            lineage = ir.init_lineages.get(int(fact.sm_tid))
            expected_pieces = [
                (0, int(fact.pm_rank0_tid)), (1, int(fact.pm_rank1_tid))
            ]
            expected_shapes = [
                list(fact.shard_shape), list(fact.shard_shape)
            ]
            if (
                lineage is None
                or int(lineage.ts) != int(fact.sm_tid)
                or lineage.tps != expected_pieces
                or lineage.tpShapes != expected_shapes
                or tuple(lineage.tsShape) != tuple(fact.full_shape)
                or int(lineage.gatherDim or 0) != int(fact.dim)
                or lineage.replicated
                or int(fact.sm_tid) not in ir.full_init_goal_ids
                or ir.pm_num_ranks != 2
            ):
                raise ValueError(
                    f"gather authority {fact_id} is not an exact two-rank init lineage"
                )
            goal = f"{generated_ns}.initGoal_{fact.sm_tid}"
            body.extend([
                f"  have hi := hInit {goal} (by native_decide)",
                "  refine ⟨?_, ?_, ?_, ?_⟩",
                f"  · exact InitGoalHolds.gather2_dim {goal} initSM initPM",
                (f"      {fact.sm_tid} {fact.pm_rank0_tid} {fact.pm_rank1_tid} "
                 f"{fact.dim} {_lean_shape_tuple(fact.shard_shape)}"),
                "      hi rfl rfl rfl rfl rfl (by native_decide)",
                f"  · exact hSM {fact.sm_tid} {_lean_shape_tuple(fact.full_shape)} (by native_decide)",
                f"  · exact hPM {fact.pm_rank0_tid} {_lean_shape_tuple(fact.shard_shape)} (by native_decide)",
                f"  · exact hPM {fact.pm_rank1_tid} {_lean_shape_tuple(fact.shard_shape)} (by native_decide)",
            ])
        elif fact.kind == "packed_cu":
            matches = [
                index for index, contract in enumerate(ir.packed_cu_contracts)
                if (
                    contract.side == fact.side
                    and contract.tid == fact.tid
                    and contract.total_tokens == fact.total_tokens
                    and contract.num_ranks == fact.num_ranks
                )
            ]
            if len(matches) != 1:
                raise ValueError(
                    f"packed authority {fact_id} lacks one exact external contract"
                )
            body.append(f"  exact hPacked_{matches[0]}")
        elif fact.kind == "label_bound":
            matches = [
                index for index, contract in enumerate(ir.tensor_value_bound_contracts)
                if (
                    contract.side == fact.side
                    and contract.tid == fact.tid
                    and contract.length == fact.length
                    and contract.upper_bound == fact.upper_bound
                )
            ]
            if len(matches) != 1:
                raise ValueError(
                    f"label-bound authority {fact_id} lacks one exact external contract"
                )
            body.append(f"  exact hBound_{matches[0]}")
        else:
            raise ValueError(f"unsupported initial authority kind {fact.kind!r}")
        blocks.append("\n".join(body))

    state_helper = f"{namespace}_initial_state"
    blocks.extend([
        f"private theorem {state_helper}",
        common_args,
        f"    : {initial.state_id}.Holds initSM initPM := by",
        "  intro fact hfact",
        f"  unfold {initial.state_id} at hfact",
        "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfact",
    ])
    for fact_id in initial.fact_ids[:-1]:
        blocks.extend([
            "  rcases hfact with rfl | hfact",
            f"  · exact {helpers[fact_id]} {call_args}",
        ])
    blocks.extend([
        "  subst fact",
        f"  exact {helpers[initial.fact_ids[-1]]} {call_args}",
    ])
    return "\n".join(blocks) + "\n"


def render_closed_public_theorem(
    ir: GoalIR,
    relation,
    namespace: str,
) -> str:
    """Render the exact public theorem from one kernel-proved joined target."""
    _validate_closed_namespace(namespace)
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("public theorem requires a complete closed chain")
    targets = [
        fact for fact in chain.relation_facts
        if fact.fact_id == chain.terminal_target_fact_id
    ]
    if len(targets) != 1 or targets[0].kind not in {
        "joined_ordinary", "joined_indexed_stack_dim1",
    }:
        raise ValueError("public theorem requires one joined terminal fact")
    target = targets[0]
    lineage_tids = [int(piece[1]) for piece in ir.lineage.tps]
    if ir.lineage.replicated or lineage_tids != [target.joined_pm_tid]:
        raise ValueError("joined terminal output does not match singleton public lineage")
    if (
        target.sm_tid != int(ir.lineage.ts)
        or tuple(target.full_shape) != tuple(ir.lineage.tsShape)
        or [list(target.full_shape)] != ir.lineage.tpShapes
    ):
        raise ValueError("joined terminal shape does not match public lineage")

    external = render_closed_external_initial_state(ir, relation, namespace)
    _, call_args, contract_names = _external_contract_arguments(ir)
    statement = getattr(ir, "public_statement_ref", "")
    if not statement:
        raise ValueError("public theorem requires an exact parsed statement reference")
    goal = getattr(ir, "lineage_ref", "")
    if not goal:
        raise ValueError("public theorem requires an exact parsed lineage reference")
    chain_name = f"{namespace}_chain"
    pm_store = f"denoteGraphDistributedFaithful {ir.pm_graph_ref} initPM"
    joined_tid = target.joined_pm_tid
    lines = [
        external.rstrip(),
        "",
        f"theorem prove_goal_{ir.n}_closed : {statement} := by",
        f"  unfold {statement}",
        *(
            ["  unfold CoarseLineageHoldsWithInitDistributedFaithfulWithContract"]
            if ir.public_statement_uses_contract_wrapper else []
        ),
        "  intro initSM initPM hSM hPM hInit hContract",
        f"  rcases hContract with ⟨{', '.join(contract_names)}⟩",
        f"  have hpre := {namespace}_initial_state {call_args}",
        "  have htarget := faithful_closed_dep_chain_extract",
        f"    {ir.sm_graph_ref} {ir.pm_graph_ref} {chain_name}",
        "    initSM initPM hpre",
        f"    {chain_name}_sm_nodes {chain_name}_pm_nodes",
        f"    {target.fact_id} (by native_decide)",
        f"  unfold {target.fact_id} RelationFact.Holds at htarget",
        "  refine ⟨htarget.full_shape, ?_, ?_⟩",
        (
            f"  · change [({pm_store} {joined_tid}).shape] = "
            f"[{_lean_shape_tuple(target.full_shape)}]"
        ),
        "    rw [← htarget.public_value, htarget.full_shape]",
        (
            f"  · rw [reconstructForGoal_of_not_replicated {goal} "
            f"{ir.pm_graph_ref}.numRanks _ rfl]"
        ),
        (
            f"    simpa only [{goal}, List.map, reconstructWithDim_singleton] "
            "using htarget.public_value"
        ),
    ]
    return "\n".join(lines) + "\n"



def _closed_bundle_module_header(
    comment: str, imports: list[str], namespace: str
) -> str:
    return "\n".join([
        f"/- AUTO-GENERATED {comment}. -/",
        *(f"import {module}" for module in imports),
        "",
        "open TrainVerify.Denote",
        "open TrainVerify.Denote.RelationCompiler",
        "",
        f"namespace TrainVerify.Denote.{namespace}",
        "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 500000",
        "noncomputable section",
        "",
    ])


def _closed_bundle_module_footer(namespace: str) -> str:
    return f"\nend\nend TrainVerify.Denote.{namespace}\n"


def _pack_closed_declaration_blocks(
    blocks: list[str], *, comment: str, imports: list[str], namespace: str,
    stem: str, max_source_bytes: int,
) -> list[tuple[str, bytes]]:
    """Greedily pack declarations without changing declaration bytes."""
    if not blocks:
        raise ValueError(f"closed bundle {stem} declarations are empty")
    footer = _closed_bundle_module_footer(namespace)
    packed: list[tuple[str, bytes]] = []
    current: list[str] = []
    for block in blocks:
        index = len(packed)
        header = _closed_bundle_module_header(comment, imports, namespace)
        candidate = header + "\n\n".join([*current, block]) + footer
        if len(candidate.encode("utf-8")) >= max_source_bytes and current:
            source = header + "\n\n".join(current) + footer
            packed.append((f"{stem}{index:03d}.lean", source.encode("utf-8")))
            current = [block]
        else:
            current.append(block)
        source = header + "\n\n".join(current) + footer
        if len(source.encode("utf-8")) >= max_source_bytes:
            raise ValueError(
                f"closed bundle declaration block exceeds source cap in {stem}: "
                f"{len(source.encode('utf-8'))} >= {max_source_bytes}"
            )
    index = len(packed)
    header = _closed_bundle_module_header(comment, imports, namespace)
    source = header + "\n\n".join(current) + footer
    packed.append((f"{stem}{index:03d}.lean", source.encode("utf-8")))
    return packed


def _closed_bundle_relation_blocks(chain, namespace: str) -> tuple[list[str], list[str]]:
    declarations = render_closed_relation_declarations(chain, namespace)
    body_start = declarations.index("noncomputable section\n") + len("noncomputable section\n")
    footer = _closed_bundle_module_footer(namespace)
    if not declarations.endswith(footer):
        raise ValueError("closed bundle relation declarations have an unexpected boundary")
    body = declarations[body_start:-len(footer)].strip()
    blocks = [block.strip() for block in body.split("\n\n") if block.strip()]
    fact_blocks: list[str] = []
    state_blocks: list[str] = []
    saw_state = False
    for block in blocks:
        is_state = bool(re.match(r"private def state_[A-Za-z0-9_]+\s*:", block))
        saw_state = saw_state or is_state
        if saw_state and not is_state:
            raise ValueError("closed bundle declarations interleave facts and states")
        public_block = re.sub(r"^private def ", "def ", block, count=1)
        (state_blocks if is_state else fact_blocks).append(public_block)
    return fact_blocks, state_blocks


def _promote_closed_segment(segment_id: str, source: str) -> str:
    pattern = (
        rf"(?m)^private(?: noncomputable)? def {re.escape(segment_id)}"
        r"(?=\s*(?::|\(smGraph pmGraph : GraphDecl\)))"
    )
    promoted, count = re.subn(pattern, f"noncomputable def {segment_id}", source, count=1)
    if count != 1:
        raise ValueError(f"closed segment {segment_id} has no promotable certificate")
    return promoted


def _validate_closed_bundle(
    bundle: dict[str, bytes], module_prefix: str, max_source_bytes: int,
    expected_segments: int,
) -> None:
    if not bundle or list(bundle)[-2:] != ["Chain.lean", "Public.lean"]:
        raise ValueError("closed bundle lacks terminal chain/public modules")
    module_order = {
        f"{module_prefix}.{path[:-5]}": index for index, path in enumerate(bundle)
    }
    segment_count = 0
    for index, (path, payload) in enumerate(bundle.items()):
        if len(payload) >= max_source_bytes:
            raise ValueError(
                f"closed bundle source cap exceeded: {path} "
                f"{len(payload)} >= {max_source_bytes}"
            )
        try:
            source = payload.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ValueError(f"closed bundle source is not UTF-8: {path}") from exc
        if path.startswith("Segment"):
            segment_count += 1
        for imported in re.findall(r"(?m)^import (\S+)$", source):
            if imported in module_order and module_order[imported] >= index:
                raise ValueError(f"closed bundle import DAG is cyclic: {path} -> {imported}")
    if segment_count != expected_segments:
        raise ValueError(
            f"closed bundle omitted segments: emitted {segment_count}, expected {expected_segments}"
        )


def compose_closed_dependent_bundle(
    ir: GoalIR, relation, namespace: str, module_prefix: str, *,
    max_source_bytes: int = 2_500_000,
) -> dict[str, bytes]:
    """Render a deterministic bounded multi-module closed public proof bundle."""
    _validate_closed_namespace(namespace)
    if not re.fullmatch(
        r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*", module_prefix
    ):
        raise ValueError(f"invalid closed bundle module prefix: {module_prefix!r}")
    if max_source_bytes <= 0:
        raise ValueError("closed bundle source cap must be positive")
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete or not chain.segments:
        raise ValueError("closed bundle requires a complete nonempty chain")

    fact_blocks, state_blocks = _closed_bundle_relation_blocks(chain, namespace)
    facts = _pack_closed_declaration_blocks(
        fact_blocks, comment="closed relation facts", imports=["denote.RelationCompiler"],
        namespace=namespace, stem="Facts", max_source_bytes=max_source_bytes,
    )
    fact_modules = [f"{module_prefix}.{path[:-5]}" for path, _ in facts]
    states = _pack_closed_declaration_blocks(
        state_blocks, comment="closed relation states", imports=fact_modules,
        namespace=namespace, stem="States", max_source_bytes=max_source_bytes,
    )
    state_modules = [f"{module_prefix}.{path[:-5]}" for path, _ in states]

    bundle: dict[str, bytes] = {}
    bundle.update(facts)
    bundle.update(states)
    rendered_segments: list[tuple[object, str, bool, str]] = []
    transitions = {item.transition_id: item for item in relation.transition_specs}
    for index, segment in enumerate(chain.segments):
        family = tuple(transitions[item].rule_id for item in segment.transition_ids)
        try:
            raw_source = render_closed_segment(ir, relation, segment.segment_id)
        except ValueError as exc:
            raise ValueError(
                f"closed bundle stopped at {segment.segment_id} family {family!r}: {exc}"
            ) from exc
        escaped_segment_id = re.escape(segment.segment_id)
        parameterized = re.search(
            rf"private(?: noncomputable)? def {escaped_segment_id}\s+"
            r"\(smGraph pmGraph : GraphDecl\)\s*:", raw_source,
        )
        concrete = re.search(
            rf"private(?: noncomputable)? def {escaped_segment_id}\s*:", raw_source,
        )
        if bool(parameterized) == bool(concrete):
            raise ValueError(
                f"closed segment {segment.segment_id} must declare exactly one concrete "
                "or graph-parameterized certificate"
            )
        promoted = _promote_closed_segment(segment.segment_id, raw_source)
        path = f"Segment{index:06d}.lean"
        header = _closed_bundle_module_header(
            f"closed segment {index:06d}",
            [ir.public_statement_module, *state_modules], namespace,
        )
        source = header + promoted.strip() + _closed_bundle_module_footer(namespace)
        payload = source.encode("utf-8")
        if len(payload) >= max_source_bytes:
            raise ValueError(
                f"closed segment source cap exceeded: {path} "
                f"{len(payload)} >= {max_source_bytes}"
            )
        bundle[path] = payload
        rendered_segments.append((segment, promoted, bool(concrete), path))

    segment_modules = [f"{module_prefix}.{path[:-5]}" for *_, path in rendered_segments]
    states_by_id = {item.state_id: item for item in chain.states}
    final_state = states_by_id[chain.segments[-1].post_state_id]
    suffix_name = f"{namespace}_suffix_{len(rendered_segments):06d}"
    chain_lines = [
        f"private noncomputable def {suffix_name} :",
        (
            f"    ClosedDepCertificateChain {ir.sm_graph_ref} {ir.pm_graph_ref} "
            f"{final_state.state_id} {final_state.state_id} :="
        ),
        f"  .nil {final_state.state_id}", "",
    ]
    for index in range(len(rendered_segments) - 1, -1, -1):
        segment, _, concrete_graphs, _ = rendered_segments[index]
        next_name = suffix_name
        suffix_name = f"{namespace}_suffix_{index:06d}"
        head = segment.segment_id if concrete_graphs else (
            f"({segment.segment_id} {ir.sm_graph_ref} {ir.pm_graph_ref})"
        )
        chain_lines.extend([
            f"private noncomputable def {suffix_name} :",
            (
                f"    ClosedDepCertificateChain {ir.sm_graph_ref} {ir.pm_graph_ref} "
                f"{segment.pre_state_id} {final_state.state_id} :="
            ),
            f"  .cons {head} {next_name}", "",
        ])
    first_state = states_by_id[chain.segments[0].pre_state_id]
    chain_name = f"{namespace}_chain"
    chain_lines.extend([
        f"noncomputable def {chain_name} :",
        (
            f"    ClosedDepCertificateChain {ir.sm_graph_ref} {ir.pm_graph_ref} "
            f"{first_state.state_id} {final_state.state_id} :="
        ),
        f"  {suffix_name}", "",
        (
            f"theorem {chain_name}_sm_nodes : {chain_name}.smNodes = "
            f"{ir.sm_graph_ref}.nodes := by"
        ), "  rfl", "",
        (
            f"theorem {chain_name}_pm_nodes : {chain_name}.pmNodes = "
            f"{ir.pm_graph_ref}.nodes := by"
        ), "  rfl", "",
    ])
    chain_source = _closed_bundle_module_header(
        "exact closed chain", segment_modules, namespace
    ) + "\n".join(chain_lines) + _closed_bundle_module_footer(namespace)
    bundle["Chain.lean"] = chain_source.encode("utf-8")

    public_body = render_closed_public_theorem(ir, relation, namespace)
    public_source = _closed_bundle_module_header(
        "external initial state and public theorem", [f"{module_prefix}.Chain"], namespace
    ) + public_body.strip() + _closed_bundle_module_footer(namespace)
    bundle["Public.lean"] = public_source.encode("utf-8")
    _validate_closed_bundle(bundle, module_prefix, max_source_bytes, len(chain.segments))
    return bundle

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
            f"({segment.segment_id} {ir.sm_graph_ref} {ir.pm_graph_ref})"
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
        "  rfl",
        "",
        f"theorem {chain_name}_pm_nodes : {chain_name}.pmNodes = {ir.pm_graph_ref}.nodes := by",
        "  rfl",
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
