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


def compose_full_topology(ir: GoalIR, module_prefix: str) -> CompositionResult:
    match = _match_hidden_embedding_alltoall_two(ir)
    if isinstance(match, CompositionResult):
        return match
    return CompositionResult(
        "embedding-hidden-alltoall-two",
        _render_hidden_embedding_alltoall_two(ir, match, module_prefix),
        (),
    )
