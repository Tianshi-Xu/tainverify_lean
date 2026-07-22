import denote.GeneratedYOCOMoE

set_option linter.style.nativeDecide false

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.ReplicaGroupWitness

private def n0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10], outs := [100] }

private def n1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag", ins := [11], outs := [101] }

private def logical : LogicalNodeId :=
  { cid := 7, mb := 0, irname := "wrap_zigzag_allgather_attn_varlen_func" }

private def orderedGroup : ReplicaGroupDecl :=
  { logical := logical,
    members := [
      { rank := 1, primaryOutTid := 101 },
      { rank := 0, primaryOutTid := 100 }
    ] }

private def orderedGraph : GraphDecl :=
  { numRanks := 2, nodes := [n0, n1], replicaGroups := [orderedGroup] }

/-- Declared process-group order is semantic; buddy lookup must not rank-sort it. -/
example : orderedGraph.replicaBuddies n0 = [n1, n0] := by native_decide

/-- Missing metadata fails closed rather than guessing peers from op/params/tids. -/
example : ({ numRanks := 2, nodes := [n0, n1] } : GraphDecl).replicaBuddies n0 = [n0] := by
  native_decide

private def duplicateRankGroup : ReplicaGroupDecl :=
  { logical := logical,
    members := [
      { rank := 0, primaryOutTid := 100 },
      { rank := 0, primaryOutTid := 101 }
    ] }

/-- Malformed duplicate-rank metadata also fails closed. -/
example :
    (({ numRanks := 2, nodes := [n0, n1], replicaGroups := [duplicateRankGroup] } : GraphDecl)
      |>.replicaBuddies n0) = [n0] := by
  native_decide

/-- The pinned A0.4B graph has one exact group per cross-rank logical call. -/
example : pm.replicaGroups.length = 50 := by native_decide

/-- Layer-0 sliding replicas are paired by SM alignment identity, despite distinct PM cids. -/
example : pm.replicaGroups.head? = some {
    logical := { cid := 14, mb := 0, irname := "wrap_sliding_window_attn_func" },
    members := [
      { rank := 0, primaryOutTid := 7437 },
      { rank := 1, primaryOutTid := 7438 }
    ]
  } := by native_decide

/-- The first generated MoE call resolves the exact two expert-weight shards in
    declared `[rank0, rank1]` order (actual five-input ordering locked here). -/
example : pm.replicaBuddies
    { rank := 0, op := "OpName.FW_all2all_moe_gmm",
      ins := [11941, 7481, 7483, 7487, 7489], outs := [7491],
      params := [64, 0, 32, 8] } =
    [{ rank := 0, op := "OpName.FW_all2all_moe_gmm",
       ins := [11941, 7481, 7483, 7487, 7489], outs := [7491],
       params := [64, 0, 32, 8] },
     { rank := 1, op := "OpName.FW_all2all_moe_gmm",
       ins := [11942, 7482, 7484, 7488, 7490], outs := [7492],
       params := [64, 32, 64, 8] }] := by native_decide

end TrainVerify.Denote.ReplicaGroupWitness
