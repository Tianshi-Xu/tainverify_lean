/-
Regression contracts for replicated and sharded-K/V zigzag attention collectives.
-/
import denote.DenoteDistributedFaithful

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote
namespace ZigzagShardedKVRegression
noncomputable section
set_option maxHeartbeats 4000000

/-- CP1 sharded-K/V attention is the communication-free local call. -/
theorem sharded_kv_cpSize_one_formula
    (qShards kShards vShards : List Tensor) (cuQ cuKV : Tensor)
    (qHeads kvHeads qDim vDim cpRank : Nat) (causal : Bool) (window : Nat) :
    fw_attn_zigzag_collective_sharded_kv qShards kShards vShards cuQ cuKV
        qHeads kvHeads qDim vDim causal window 1 cpRank =
      fw_attn_varlen
        (qShards.getD cpRank (zeroTensor []))
        (kShards.getD cpRank (zeroTensor []))
        (vShards.getD cpRank (zeroTensor []))
        cuQ cuKV qHeads kvHeads qDim vDim causal window := by
  rw [fw_attn_zigzag_collective_sharded_kv_cpSize_one]

/-- CP2 sharded-K/V attention unshuffles only Q, gathers K/V directly, then
chunks and reshuffles the full attention result. -/
theorem sharded_kv_cpSize_two_formula
    (qShards kShards vShards : List Tensor) (cuQ cuKV : Tensor)
    (qHeads kvHeads qDim vDim cpRank : Nat) (causal : Bool) (window : Nat) :
    fw_attn_zigzag_collective_sharded_kv qShards kShards vShards cuQ cuKV
        qHeads kvHeads qDim vDim causal window 2 cpRank =
      let decodedCuQ := decodeCuSeqlens cuQ
      let linearQShards := (List.range 2).map (fun r =>
        fw_maybe_unshuffle_collective qShards decodedCuQ 2 r)
      let fullQ := allGatherPrimDimN 0 2 0 linearQShards
      let fullK := allGatherPrimDimN 0 2 0 kShards
      let fullV := allGatherPrimDimN 0 2 0 vShards
      let fullOut := fw_attn_varlen fullQ fullK fullV cuQ cuKV
        qHeads kvHeads qDim vDim causal window
      let linearOutShards := (List.range 2).map (fun r =>
        chunkPrimDimN 0 2 r fullOut)
      fw_maybe_shuffle_collective linearOutShards decodedCuQ 2 cpRank := by
  unfold fw_attn_zigzag_collective_sharded_kv
  rw [if_neg (by decide : (2 : Nat) ≠ 1)]

/-- The pre-existing replicated-K/V CP1 contract remains unchanged. -/
theorem replicated_kv_cpSize_one_formula
    (qShards : List Tensor) (k v cuQ cuKV : Tensor)
    (qHeads kvHeads qDim vDim cpRank : Nat) (causal : Bool) (window : Nat) :
    fw_attn_zigzag_collective qShards k v cuQ cuKV
        qHeads kvHeads qDim vDim causal window 1 cpRank =
      fw_attn_varlen (qShards.getD cpRank (zeroTensor [])) k v cuQ cuKV
        qHeads kvHeads qDim vDim causal window := by
  rw [fw_attn_zigzag_collective_cpSize_one]

/-- The pre-existing replicated-K/V CP2 contract still does not gather K/V. -/
theorem replicated_kv_cpSize_two_formula
    (qShards : List Tensor) (k v cuQ cuKV : Tensor)
    (qHeads kvHeads qDim vDim cpRank : Nat) (causal : Bool) (window : Nat) :
    fw_attn_zigzag_collective qShards k v cuQ cuKV
        qHeads kvHeads qDim vDim causal window 2 cpRank =
      let decodedCuQ := decodeCuSeqlens cuQ
      let linearQShards := (List.range 2).map (fun r =>
        fw_maybe_unshuffle_collective qShards decodedCuQ 2 r)
      let fullQ := allGatherPrimDimN 0 2 0 linearQShards
      let fullOut := fw_attn_varlen fullQ k v cuQ cuKV
        qHeads kvHeads qDim vDim causal window
      let linearOutShards := (List.range 2).map (fun r =>
        chunkPrimDimN 0 2 r fullOut)
      fw_maybe_shuffle_collective linearOutShards decodedCuQ 2 cpRank := by
  unfold fw_attn_zigzag_collective
  rw [if_neg (by decide : (2 : Nat) ≠ 1)]

private def n0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10, 20, 30, 40, 41], outs := [50], params := [2, 2, 1, 1, 1, 0] }
private def n1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11, 21, 31, 40, 41], outs := [51], params := [2, 2, 1, 1, 1, 0] }
private def n1Shared : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11, 20, 30, 40, 41], outs := [51], params := [2, 2, 1, 1, 1, 0] }
private def logical : LogicalNodeId :=
  { cid := 7, mb := 0, irname := "wrap_zigzag_allgather_attn_varlen_func" }
private def g : GraphDecl :=
  { numRanks := 2, nodes := [n0, n1], replicaGroups :=
      [{ logical := logical, members := [{ rank := 0, primaryOutTid := 50 },
        { rank := 1, primaryOutTid := 51 }] }] }
private def gShared : GraphDecl :=
  { numRanks := 2, nodes := [n0, n1Shared], replicaGroups :=
      [{ logical := logical, members := [{ rank := 0, primaryOutTid := 50 },
        { rank := 1, primaryOutTid := 51 }] }] }
private theorem buddies : g.replicaBuddies n0 = [n0, n1] := by native_decide
private theorem buddiesShared : gShared.replicaBuddies n0 = [n0, n1Shared] := by native_decide

/-- Distinct buddy K/V tids select the wrapper's sharded-K/V gather path. -/
theorem graph_dispatches_distinct_kv_to_sharded (s : Store) :
    applyNodeFaithfulZigzagAttnValue g s n0 =
      fw_attn_zigzag_collective_sharded_kv
        [s 10, s 11] [s 20, s 21] [s 30, s 31]
        (s 40) (s 41) 2 2 1 1 true 0 2 0 := by
  unfold applyNodeFaithfulZigzagAttnValue
  rw [buddies]
  rfl

/-- Shared buddy K/V tids select the legacy replicated-K/V path. -/
theorem graph_classifies_shared_kv_as_replicated :
    zigzagAttnUsesReplicatedKV gShared n0 = true := by native_decide

#print axioms graph_dispatches_distinct_kv_to_sharded
#print axioms graph_classifies_shared_kv_as_replicated
end
end ZigzagShardedKVRegression
end TrainVerify.Denote
