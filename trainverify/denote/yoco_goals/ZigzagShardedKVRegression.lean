/-
Regression: faithful zigzag attention collects rank-local K/V buddies and gathers
those shards in declared rank order before invoking attention.
-/
import denote.DenoteDistributedFaithful

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.ZigzagShardedKVRegression
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.nativeDecide false

private def n0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10, 20, 30, 40, 41], outs := [50], params := [2, 2, 1, 1, 1, 0] }

private def n1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11, 21, 31, 40, 41], outs := [51], params := [2, 2, 1, 1, 1, 0] }

private def g : GraphDecl :=
  { numRanks := 2
    nodes := [n0, n1]
    replicaGroups :=
      [{ logical := { cid := 0, mb := 0, irname := "attn" },
         members := [{ rank := 0, primaryOutTid := 50 },
                     { rank := 1, primaryOutTid := 51 }] }] }

private theorem buddies : g.replicaBuddies n0 = [n0, n1] := by
  native_decide

/-- Both buddies' distinct K/V inputs reach dim-0 gathers in declared rank order;
K/V are not passed through the Q unshuffle. -/
theorem buddy_kv_are_rank_ordered_gathers (s : Store) :
    applyNodeFaithfulZigzagAttnValue g s n0 =
      let qs := [s 10, s 11]
      let linearQs := (List.range 2).map (fun r =>
        fw_maybe_unshuffle_collective qs (decodeCuSeqlens (s 40)) 2 r)
      let fullOut := fw_attn_varlen
        (allGatherPrimDimN 0 2 0 linearQs)
        (allGatherPrimDimN 0 2 0 [s 20, s 21])
        (allGatherPrimDimN 0 2 0 [s 30, s 31])
        (s 40) (s 41) 2 2 1 1 true 0
      fw_maybe_shuffle_collective
        ((List.range 2).map (fun r => chunkPrimDimN 0 2 r fullOut))
        (decodeCuSeqlens (s 40)) 2 0 := by
  unfold applyNodeFaithfulZigzagAttnValue
  rw [buddies]
  rfl

end
end TrainVerify.Denote.ZigzagShardedKVRegression
