import denote.GraphGears
import denote.BWEmbeddingHiddenShardK
import denote.RelationCompiler
open TrainVerify.Denote

namespace BWHiddenGraphK1B3S2V11D5
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }] }
def pm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [103], outs := [104] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 101], outs := [102] }, { rank := 0, op := "OpName.FW_float", ins := [103], outs := [105] }] }
end BWHiddenGraphK1B3S2V11D5
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWHiddenK1B3S2V11D5

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100] 2 [3, 2, 5] [3, 2, 5]

private def fact_i : RelationFact :=
  .sharded 2 [2] 0 [3, 2] [3, 2]

private def fact_w : RelationFact :=
  .sharded 3 [101] 1 [11, 5] [11, 5]

private def fact_o : RelationFact :=
  .sharded 4 [102] 1 [11, 5] [11, 5]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [3, 2, 5]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [103], outs := [104] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 101], outs := [102] }, { rank := 0, op := "OpName.FW_float", ins := [103], outs := [105] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK1B3S2V11D5.sm smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK1B3S2V11D5.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK1B3S2V11D5.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK1B3S2V11D5.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK1B3S2V11D5.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 102 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 101], outs := [102] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 102 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore 101) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK1B3S2V11D5.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 101], outs := [102] } 102
      (fun t => bw_embedding (t 100) (t 2) (t 101)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK1B3S2V11D5.pm t 0 100 2 101 102
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK1B3S2V11D5.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 101], outs := [102] } :: (segment_000000_pm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK1B3S2V11D5.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 101], outs := [102] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK1B3S2V11D5.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 101], outs := [102] } :: (segment_000000_pm_nodes.drop 2)) 101
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 102 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK1B3S2V11D5.pm) pmStore 101) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100] 2 [3, 2, 5] [3, 2, 5] at hg
  have hgV : smFinal 1 = allGatherPrimDimN 2 1 0 [pmFinal 100] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 2] 0 [3, 2] [3, 2] at hi
  have hiShape := hi.shard_shapes (pmFinal 2) (by simp)
  have hiEq : smFinal 2 = pmFinal 2 := by
    rw [hi.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 101] 1 [11, 5] [11, 5] at hw
  have hwV : smFinal 3 = allGatherPrimDimN 1 1 0 [pmFinal 101] := by
    simpa only [List.length_cons, List.length_nil] using hw.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 102 = bw_embedding (pmFinal 100) (pmFinal 2) (pmFinal 101) at hPm0
  have houtShape0 : (pmFinal 102).shape = [11, 5] := by
    rw [hPm0, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 101) (by simp)
  have hComm := TrainVerify.Denote.bw_embedding_hidden_allGather_rank3 1 3 2 11 5
    [pmFinal 100] [pmFinal 101] (pmFinal 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape
  simp only [List.zipWith] at hComm
  have hValue : smFinal 4 = allGatherPrimDimN 1 1 0 [pmFinal 102] := by
    rw [hSm, hgV, hiEq, hwV, hComm]
    rw [← hPm0]
  have hValueL : smFinal 4 = allGatherPrimDimN 1 [pmFinal 102].length 0 [pmFinal 102] := by
    simpa only [List.length_cons, List.length_nil] using hValue
  have hFullShape : (smFinal 4).shape = [11, 5] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hout : fact_o.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 4) [pmFinal 102] 1 [11, 5] [11, 5]
    refine {
      full_value := hValueL
      full_shape := hFullShape
      shards_nonempty := by simp
      gather_dim_lt := by native_decide
      shard_shapes := ?_
      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
    }
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl
    · exact houtShape0
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate BWHiddenGraphK1B3S2V11D5.sm BWHiddenGraphK1B3S2V11D5.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWHiddenK1B3S2V11D5
open TrainVerify.Denote

namespace BWHiddenGraphK2B1S16V256D32
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }] }
def pm : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [106], outs := [107] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 102], outs := [104] }, { rank := 1, op := "OpName.FW_float", ins := [106], outs := [108] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 103], outs := [105] }, { rank := 0, op := "OpName.FW_float", ins := [106], outs := [109] }] }
end BWHiddenGraphK2B1S16V256D32
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWHiddenK2B1S16V256D32

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100, 101] 2 [1, 16, 64] [1, 16, 32]

private def fact_i : RelationFact :=
  .sharded 2 [2] 0 [1, 16] [1, 16]

private def fact_w : RelationFact :=
  .sharded 3 [102, 103] 1 [256, 64] [256, 32]

private def fact_o : RelationFact :=
  .sharded 4 [104, 105] 1 [256, 64] [256, 32]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [1, 16, 64]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [106], outs := [107] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 102], outs := [104] }, { rank := 1, op := "OpName.FW_float", ins := [106], outs := [108] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 103], outs := [105] }, { rank := 0, op := "OpName.FW_float", ins := [106], outs := [109] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK2B1S16V256D32.sm smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK2B1S16V256D32.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK2B1S16V256D32.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK2B1S16V256D32.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK2B1S16V256D32.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 104 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 102) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 102], outs := [104] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 104 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 102) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK2B1S16V256D32.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 102], outs := [104] } 104
      (fun t => bw_embedding (t 100) (t 2) (t 102)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK2B1S16V256D32.pm t 0 100 2 102 104
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK2B1S16V256D32.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 102], outs := [104] } :: (segment_000000_pm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK2B1S16V256D32.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 102], outs := [104] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK2B1S16V256D32.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 102], outs := [104] } :: (segment_000000_pm_nodes.drop 2)) 102
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 104 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 102) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 102) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 102) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 105 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 103) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 103], outs := [105] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 105 = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 101) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 103) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK2B1S16V256D32.pm pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 103], outs := [105] } 105
      (fun t => bw_embedding (t 101) (t 2) (t 103)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK2B1S16V256D32.pm t 1 101 2 103 105
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK2B1S16V256D32.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 103], outs := [105] } :: (segment_000000_pm_nodes.drop 4)) 101
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK2B1S16V256D32.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 103], outs := [105] } :: (segment_000000_pm_nodes.drop 4)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK2B1S16V256D32.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 103], outs := [105] } :: (segment_000000_pm_nodes.drop 4)) 103
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 105 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 103) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 101) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK2B1S16V256D32.pm) pmStore 103) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 103) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101] 2 [1, 16, 64] [1, 16, 32] at hg
  have hgV : smFinal 1 = allGatherPrimDimN 2 2 0 [pmFinal 100, pmFinal 101] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 2] 0 [1, 16] [1, 16] at hi
  have hiShape := hi.shard_shapes (pmFinal 2) (by simp)
  have hiEq : smFinal 2 = pmFinal 2 := by
    rw [hi.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 102, pmFinal 103] 1 [256, 64] [256, 32] at hw
  have hwV : smFinal 3 = allGatherPrimDimN 1 2 0 [pmFinal 102, pmFinal 103] := by
    simpa only [List.length_cons, List.length_nil] using hw.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 104 = bw_embedding (pmFinal 100) (pmFinal 2) (pmFinal 102) at hPm0
  have houtShape0 : (pmFinal 104).shape = [256, 32] := by
    rw [hPm0, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 102) (by simp)
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 105 = bw_embedding (pmFinal 101) (pmFinal 2) (pmFinal 103) at hPm1
  have houtShape1 : (pmFinal 105).shape = [256, 32] := by
    rw [hPm1, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 103) (by simp)
  have hComm := TrainVerify.Denote.bw_embedding_hidden_allGather_rank3 2 1 16 256 32
    [pmFinal 100, pmFinal 101] [pmFinal 102, pmFinal 103] (pmFinal 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape
  simp only [List.zipWith] at hComm
  have hValue : smFinal 4 = allGatherPrimDimN 1 2 0 [pmFinal 104, pmFinal 105] := by
    rw [hSm, hgV, hiEq, hwV, hComm]
    rw [← hPm0, ← hPm1]
  have hValueL : smFinal 4 = allGatherPrimDimN 1 [pmFinal 104, pmFinal 105].length 0 [pmFinal 104, pmFinal 105] := by
    simpa only [List.length_cons, List.length_nil] using hValue
  have hFullShape : (smFinal 4).shape = [256, 64] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hout : fact_o.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 4) [pmFinal 104, pmFinal 105] 1 [256, 64] [256, 32]
    refine {
      full_value := hValueL
      full_shape := hFullShape
      shards_nonempty := by simp
      gather_dim_lt := by native_decide
      shard_shapes := ?_
      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
    }
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact houtShape0
    · exact houtShape1
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate BWHiddenGraphK2B1S16V256D32.sm BWHiddenGraphK2B1S16V256D32.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWHiddenK2B1S16V256D32
open TrainVerify.Denote

namespace BWHiddenGraphK3B2S5V13D7
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }] }
def pm : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [109], outs := [110] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 103], outs := [106] }, { rank := 1, op := "OpName.FW_float", ins := [109], outs := [111] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 104], outs := [107] }, { rank := 2, op := "OpName.FW_float", ins := [109], outs := [112] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 105], outs := [108] }, { rank := 0, op := "OpName.FW_float", ins := [109], outs := [113] }] }
end BWHiddenGraphK3B2S5V13D7
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWHiddenK3B2S5V13D7

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100, 101, 102] 2 [2, 5, 21] [2, 5, 7]

private def fact_i : RelationFact :=
  .sharded 2 [2] 0 [2, 5] [2, 5]

private def fact_w : RelationFact :=
  .sharded 3 [103, 104, 105] 1 [13, 21] [13, 7]

private def fact_o : RelationFact :=
  .sharded 4 [106, 107, 108] 1 [13, 21] [13, 7]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [2, 5, 21]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [109], outs := [110] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 103], outs := [106] }, { rank := 1, op := "OpName.FW_float", ins := [109], outs := [111] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 104], outs := [107] }, { rank := 2, op := "OpName.FW_float", ins := [109], outs := [112] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 105], outs := [108] }, { rank := 0, op := "OpName.FW_float", ins := [109], outs := [113] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK3B2S5V13D7.sm smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK3B2S5V13D7.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 106 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 103) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 103], outs := [106] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 106 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 103) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 103], outs := [106] } 106
      (fun t => bw_embedding (t 100) (t 2) (t 103)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK3B2S5V13D7.pm t 0 100 2 103 106
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 103], outs := [106] } :: (segment_000000_pm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 103], outs := [106] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 103], outs := [106] } :: (segment_000000_pm_nodes.drop 2)) 103
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 106 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 103) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 103) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 103) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 107 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 104) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 104], outs := [107] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 107 = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 101) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 104) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 104], outs := [107] } 107
      (fun t => bw_embedding (t 101) (t 2) (t 104)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK3B2S5V13D7.pm t 1 101 2 104 107
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 104], outs := [107] } :: (segment_000000_pm_nodes.drop 4)) 101
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 104], outs := [107] } :: (segment_000000_pm_nodes.drop 4)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 104 = (segment_000000_pm_final pmStore) 104 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 104], outs := [107] } :: (segment_000000_pm_nodes.drop 4)) 104
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 107 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 104) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 101) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 104) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 104) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 108 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 105) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 105], outs := [108] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 108 = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 102) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 2) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 105) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 105], outs := [108] } 108
      (fun t => bw_embedding (t 102) (t 2) (t 105)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK3B2S5V13D7.pm t 2 102 2 105 108
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 105], outs := [108] } :: (segment_000000_pm_nodes.drop 6)) 102
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 105], outs := [108] } :: (segment_000000_pm_nodes.drop 6)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 105 = (segment_000000_pm_final pmStore) 105 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK3B2S5V13D7.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 105], outs := [108] } :: (segment_000000_pm_nodes.drop 6)) 105
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 108 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 105) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 102) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 2) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK3B2S5V13D7.pm) pmStore 105) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 105) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101, pmFinal 102] 2 [2, 5, 21] [2, 5, 7] at hg
  have hgV : smFinal 1 = allGatherPrimDimN 2 3 0 [pmFinal 100, pmFinal 101, pmFinal 102] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 2] 0 [2, 5] [2, 5] at hi
  have hiShape := hi.shard_shapes (pmFinal 2) (by simp)
  have hiEq : smFinal 2 = pmFinal 2 := by
    rw [hi.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 103, pmFinal 104, pmFinal 105] 1 [13, 21] [13, 7] at hw
  have hwV : smFinal 3 = allGatherPrimDimN 1 3 0 [pmFinal 103, pmFinal 104, pmFinal 105] := by
    simpa only [List.length_cons, List.length_nil] using hw.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 106 = bw_embedding (pmFinal 100) (pmFinal 2) (pmFinal 103) at hPm0
  have houtShape0 : (pmFinal 106).shape = [13, 7] := by
    rw [hPm0, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 103) (by simp)
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 107 = bw_embedding (pmFinal 101) (pmFinal 2) (pmFinal 104) at hPm1
  have houtShape1 : (pmFinal 107).shape = [13, 7] := by
    rw [hPm1, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 104) (by simp)
  have hPm2 := segment_000000_hPmWriter2 pmStore
  change pmFinal 108 = bw_embedding (pmFinal 102) (pmFinal 2) (pmFinal 105) at hPm2
  have houtShape2 : (pmFinal 108).shape = [13, 7] := by
    rw [hPm2, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 105) (by simp)
  have hComm := TrainVerify.Denote.bw_embedding_hidden_allGather_rank3 3 2 5 13 7
    [pmFinal 100, pmFinal 101, pmFinal 102] [pmFinal 103, pmFinal 104, pmFinal 105] (pmFinal 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape
  simp only [List.zipWith] at hComm
  have hValue : smFinal 4 = allGatherPrimDimN 1 3 0 [pmFinal 106, pmFinal 107, pmFinal 108] := by
    rw [hSm, hgV, hiEq, hwV, hComm]
    rw [← hPm0, ← hPm1, ← hPm2]
  have hValueL : smFinal 4 = allGatherPrimDimN 1 [pmFinal 106, pmFinal 107, pmFinal 108].length 0 [pmFinal 106, pmFinal 107, pmFinal 108] := by
    simpa only [List.length_cons, List.length_nil] using hValue
  have hFullShape : (smFinal 4).shape = [13, 21] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hout : fact_o.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 4) [pmFinal 106, pmFinal 107, pmFinal 108] 1 [13, 21] [13, 7]
    refine {
      full_value := hValueL
      full_shape := hFullShape
      shards_nonempty := by simp
      gather_dim_lt := by native_decide
      shard_shapes := ?_
      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
    }
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact houtShape0
    · exact houtShape1
    · exact houtShape2
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate BWHiddenGraphK3B2S5V13D7.sm BWHiddenGraphK3B2S5V13D7.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWHiddenK3B2S5V13D7
open TrainVerify.Denote

namespace BWHiddenGraphK4B1S16V256D16
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }] }
def pm : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [112], outs := [113] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 104], outs := [108] }, { rank := 1, op := "OpName.FW_float", ins := [112], outs := [114] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 105], outs := [109] }, { rank := 2, op := "OpName.FW_float", ins := [112], outs := [115] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [110] }, { rank := 3, op := "OpName.FW_float", ins := [112], outs := [116] }, { rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [111] }, { rank := 0, op := "OpName.FW_float", ins := [112], outs := [117] }] }
end BWHiddenGraphK4B1S16V256D16
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWHiddenK4B1S16V256D16

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100, 101, 102, 103] 2 [1, 16, 64] [1, 16, 16]

private def fact_i : RelationFact :=
  .sharded 2 [2] 0 [1, 16] [1, 16]

private def fact_w : RelationFact :=
  .sharded 3 [104, 105, 106, 107] 1 [256, 64] [256, 16]

private def fact_o : RelationFact :=
  .sharded 4 [108, 109, 110, 111] 1 [256, 64] [256, 16]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [1, 16, 64]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [112], outs := [113] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 104], outs := [108] }, { rank := 1, op := "OpName.FW_float", ins := [112], outs := [114] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 105], outs := [109] }, { rank := 2, op := "OpName.FW_float", ins := [112], outs := [115] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [110] }, { rank := 3, op := "OpName.FW_float", ins := [112], outs := [116] }, { rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [111] }, { rank := 0, op := "OpName.FW_float", ins := [112], outs := [117] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK4B1S16V256D16.sm smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK4B1S16V256D16.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 108 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 104) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 104], outs := [108] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 108 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 104) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 104], outs := [108] } 108
      (fun t => bw_embedding (t 100) (t 2) (t 104)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK4B1S16V256D16.pm t 0 100 2 104 108
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 104], outs := [108] } :: (segment_000000_pm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 104], outs := [108] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 104 = (segment_000000_pm_final pmStore) 104 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 104], outs := [108] } :: (segment_000000_pm_nodes.drop 2)) 104
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 108 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 104) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 104) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 104) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 109 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 105) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 105], outs := [109] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 109 = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 101) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 105) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 105], outs := [109] } 109
      (fun t => bw_embedding (t 101) (t 2) (t 105)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK4B1S16V256D16.pm t 1 101 2 105 109
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 105], outs := [109] } :: (segment_000000_pm_nodes.drop 4)) 101
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 105], outs := [109] } :: (segment_000000_pm_nodes.drop 4)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 105 = (segment_000000_pm_final pmStore) 105 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 105], outs := [109] } :: (segment_000000_pm_nodes.drop 4)) 105
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 109 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 105) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 101) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 105) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 105) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 110 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 106) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [110] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 110 = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 102) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 106) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [110] } 110
      (fun t => bw_embedding (t 102) (t 2) (t 106)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK4B1S16V256D16.pm t 2 102 2 106 110
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [110] } :: (segment_000000_pm_nodes.drop 6)) 102
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [110] } :: (segment_000000_pm_nodes.drop 6)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 106 = (segment_000000_pm_final pmStore) 106 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [110] } :: (segment_000000_pm_nodes.drop 6)) 106
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 110 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 106) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 102) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 106) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 106) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 111 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 107) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [111] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 111 = bw_embedding (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 103) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 107) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [111] } 111
      (fun t => bw_embedding (t 103) (t 2) (t 107)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK4B1S16V256D16.pm t 3 103 2 107 111
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [111] } :: (segment_000000_pm_nodes.drop 8)) 103
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [111] } :: (segment_000000_pm_nodes.drop 8)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 107 = (segment_000000_pm_final pmStore) 107 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK4B1S16V256D16.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [111] } :: (segment_000000_pm_nodes.drop 8)) 107
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 111 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 107) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 103) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 2) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK4B1S16V256D16.pm) pmStore 107) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 107) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] 2 [1, 16, 64] [1, 16, 16] at hg
  have hgV : smFinal 1 = allGatherPrimDimN 2 4 0 [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 2] 0 [1, 16] [1, 16] at hi
  have hiShape := hi.shard_shapes (pmFinal 2) (by simp)
  have hiEq : smFinal 2 = pmFinal 2 := by
    rw [hi.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 104, pmFinal 105, pmFinal 106, pmFinal 107] 1 [256, 64] [256, 16] at hw
  have hwV : smFinal 3 = allGatherPrimDimN 1 4 0 [pmFinal 104, pmFinal 105, pmFinal 106, pmFinal 107] := by
    simpa only [List.length_cons, List.length_nil] using hw.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 108 = bw_embedding (pmFinal 100) (pmFinal 2) (pmFinal 104) at hPm0
  have houtShape0 : (pmFinal 108).shape = [256, 16] := by
    rw [hPm0, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 104) (by simp)
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 109 = bw_embedding (pmFinal 101) (pmFinal 2) (pmFinal 105) at hPm1
  have houtShape1 : (pmFinal 109).shape = [256, 16] := by
    rw [hPm1, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 105) (by simp)
  have hPm2 := segment_000000_hPmWriter2 pmStore
  change pmFinal 110 = bw_embedding (pmFinal 102) (pmFinal 2) (pmFinal 106) at hPm2
  have houtShape2 : (pmFinal 110).shape = [256, 16] := by
    rw [hPm2, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 106) (by simp)
  have hPm3 := segment_000000_hPmWriter3 pmStore
  change pmFinal 111 = bw_embedding (pmFinal 103) (pmFinal 2) (pmFinal 107) at hPm3
  have houtShape3 : (pmFinal 111).shape = [256, 16] := by
    rw [hPm3, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 107) (by simp)
  have hComm := TrainVerify.Denote.bw_embedding_hidden_allGather_rank3 4 1 16 256 16
    [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] [pmFinal 104, pmFinal 105, pmFinal 106, pmFinal 107] (pmFinal 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape
  simp only [List.zipWith] at hComm
  have hValue : smFinal 4 = allGatherPrimDimN 1 4 0 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] := by
    rw [hSm, hgV, hiEq, hwV, hComm]
    rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
  have hValueL : smFinal 4 = allGatherPrimDimN 1 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111].length 0 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] := by
    simpa only [List.length_cons, List.length_nil] using hValue
  have hFullShape : (smFinal 4).shape = [256, 64] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hout : fact_o.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 4) [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 1 [256, 64] [256, 16]
    refine {
      full_value := hValueL
      full_shape := hFullShape
      shards_nonempty := by simp
      gather_dim_lt := by native_decide
      shard_shapes := ?_
      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
    }
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact houtShape0
    · exact houtShape1
    · exact houtShape2
    · exact houtShape3
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate BWHiddenGraphK4B1S16V256D16.sm BWHiddenGraphK4B1S16V256D16.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWHiddenK4B1S16V256D16
open TrainVerify.Denote

namespace BWHiddenGraphK5B2S3V17D11
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }] }
def pm : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [115], outs := [116] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 105], outs := [110] }, { rank := 1, op := "OpName.FW_float", ins := [115], outs := [117] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 106], outs := [111] }, { rank := 2, op := "OpName.FW_float", ins := [115], outs := [118] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 107], outs := [112] }, { rank := 3, op := "OpName.FW_float", ins := [115], outs := [119] }, { rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 108], outs := [113] }, { rank := 4, op := "OpName.FW_float", ins := [115], outs := [120] }, { rank := 4, op := "OpName.BW_embedding", ins := [104, 2, 109], outs := [114] }, { rank := 0, op := "OpName.FW_float", ins := [115], outs := [121] }] }
end BWHiddenGraphK5B2S3V17D11
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWHiddenK5B2S3V17D11

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100, 101, 102, 103, 104] 2 [2, 3, 55] [2, 3, 11]

private def fact_i : RelationFact :=
  .sharded 2 [2] 0 [2, 3] [2, 3]

private def fact_w : RelationFact :=
  .sharded 3 [105, 106, 107, 108, 109] 1 [17, 55] [17, 11]

private def fact_o : RelationFact :=
  .sharded 4 [110, 111, 112, 113, 114] 1 [17, 55] [17, 11]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [2, 3, 55]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [115], outs := [116] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 105], outs := [110] }, { rank := 1, op := "OpName.FW_float", ins := [115], outs := [117] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 106], outs := [111] }, { rank := 2, op := "OpName.FW_float", ins := [115], outs := [118] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 107], outs := [112] }, { rank := 3, op := "OpName.FW_float", ins := [115], outs := [119] }, { rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 108], outs := [113] }, { rank := 4, op := "OpName.FW_float", ins := [115], outs := [120] }, { rank := 4, op := "OpName.BW_embedding", ins := [104, 2, 109], outs := [114] }, { rank := 0, op := "OpName.FW_float", ins := [115], outs := [121] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK5B2S3V17D11.sm smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK5B2S3V17D11.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 110 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 105) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 105], outs := [110] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 110 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 105) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 105], outs := [110] } 110
      (fun t => bw_embedding (t 100) (t 2) (t 105)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK5B2S3V17D11.pm t 0 100 2 105 110
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 105], outs := [110] } :: (segment_000000_pm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 105], outs := [110] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 105 = (segment_000000_pm_final pmStore) 105 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 2, 105], outs := [110] } :: (segment_000000_pm_nodes.drop 2)) 105
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 110 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 105) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 100) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 105) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 105) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 111 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 106) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 106], outs := [111] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 111 = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 101) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 106) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 106], outs := [111] } 111
      (fun t => bw_embedding (t 101) (t 2) (t 106)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK5B2S3V17D11.pm t 1 101 2 106 111
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 106], outs := [111] } :: (segment_000000_pm_nodes.drop 4)) 101
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 106], outs := [111] } :: (segment_000000_pm_nodes.drop 4)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 106 = (segment_000000_pm_final pmStore) 106 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 2, 106], outs := [111] } :: (segment_000000_pm_nodes.drop 4)) 106
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 111 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 106) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 101) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 106) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 106) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 112 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 107) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 107], outs := [112] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 112 = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 102) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 107) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 107], outs := [112] } 112
      (fun t => bw_embedding (t 102) (t 2) (t 107)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK5B2S3V17D11.pm t 2 102 2 107 112
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 107], outs := [112] } :: (segment_000000_pm_nodes.drop 6)) 102
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 107], outs := [112] } :: (segment_000000_pm_nodes.drop 6)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 107 = (segment_000000_pm_final pmStore) 107 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 2, 107], outs := [112] } :: (segment_000000_pm_nodes.drop 6)) 107
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 112 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 107) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 102) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 107) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 107) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 113 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 108) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 108], outs := [113] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 113 = bw_embedding (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 103) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 108) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 108], outs := [113] } 113
      (fun t => bw_embedding (t 103) (t 2) (t 108)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK5B2S3V17D11.pm t 3 103 2 108 113
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 108], outs := [113] } :: (segment_000000_pm_nodes.drop 8)) 103
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 108], outs := [113] } :: (segment_000000_pm_nodes.drop 8)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 108 = (segment_000000_pm_final pmStore) 108 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_embedding", ins := [103, 2, 108], outs := [113] } :: (segment_000000_pm_nodes.drop 8)) 108
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 113 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 108) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 103) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 108) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 108) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter4 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 114 = bw_embedding ((segment_000000_pm_final pmStore) 104) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 109) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 9) ++ [{ rank := 4, op := "OpName.BW_embedding", ins := [104, 2, 109], outs := [114] }] ++ (segment_000000_pm_nodes.drop 10) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 114 = bw_embedding (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 104) (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 109) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 9) (segment_000000_pm_nodes.drop 10)
      { rank := 4, op := "OpName.BW_embedding", ins := [104, 2, 109], outs := [114] } 114
      (fun t => bw_embedding (t 104) (t 2) (t 109)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWHiddenGraphK5B2S3V17D11.pm t 4 104 2 109 114
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 104 = (segment_000000_pm_final pmStore) 104 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 4, op := "OpName.BW_embedding", ins := [104, 2, 109], outs := [114] } :: (segment_000000_pm_nodes.drop 10)) 104
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 4, op := "OpName.BW_embedding", ins := [104, 2, 109], outs := [114] } :: (segment_000000_pm_nodes.drop 10)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 109 = (segment_000000_pm_final pmStore) 109 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWHiddenGraphK5B2S3V17D11.pm pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 4, op := "OpName.BW_embedding", ins := [104, 2, 109], outs := [114] } :: (segment_000000_pm_nodes.drop 10)) 109
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 114 = bw_embedding ((segment_000000_pm_final pmStore) 104) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 109) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 104) (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 2) (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWHiddenGraphK5B2S3V17D11.pm) pmStore 109) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 104) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 109) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] 2 [2, 3, 55] [2, 3, 11] at hg
  have hgV : smFinal 1 = allGatherPrimDimN 2 5 0 [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 2] 0 [2, 3] [2, 3] at hi
  have hiShape := hi.shard_shapes (pmFinal 2) (by simp)
  have hiEq : smFinal 2 = pmFinal 2 := by
    rw [hi.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] 1 [17, 55] [17, 11] at hw
  have hwV : smFinal 3 = allGatherPrimDimN 1 5 0 [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] := by
    simpa only [List.length_cons, List.length_nil] using hw.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 110 = bw_embedding (pmFinal 100) (pmFinal 2) (pmFinal 105) at hPm0
  have houtShape0 : (pmFinal 110).shape = [17, 11] := by
    rw [hPm0, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 105) (by simp)
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 111 = bw_embedding (pmFinal 101) (pmFinal 2) (pmFinal 106) at hPm1
  have houtShape1 : (pmFinal 111).shape = [17, 11] := by
    rw [hPm1, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 106) (by simp)
  have hPm2 := segment_000000_hPmWriter2 pmStore
  change pmFinal 112 = bw_embedding (pmFinal 102) (pmFinal 2) (pmFinal 107) at hPm2
  have houtShape2 : (pmFinal 112).shape = [17, 11] := by
    rw [hPm2, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 107) (by simp)
  have hPm3 := segment_000000_hPmWriter3 pmStore
  change pmFinal 113 = bw_embedding (pmFinal 103) (pmFinal 2) (pmFinal 108) at hPm3
  have houtShape3 : (pmFinal 113).shape = [17, 11] := by
    rw [hPm3, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 108) (by simp)
  have hPm4 := segment_000000_hPmWriter4 pmStore
  change pmFinal 114 = bw_embedding (pmFinal 104) (pmFinal 2) (pmFinal 109) at hPm4
  have houtShape4 : (pmFinal 114).shape = [17, 11] := by
    rw [hPm4, bw_embedding_shape]
    exact hw.shard_shapes (pmFinal 109) (by simp)
  have hComm := TrainVerify.Denote.bw_embedding_hidden_allGather_rank3 5 2 3 17 11
    [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] (pmFinal 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape
  simp only [List.zipWith] at hComm
  have hValue : smFinal 4 = allGatherPrimDimN 1 5 0 [pmFinal 110, pmFinal 111, pmFinal 112, pmFinal 113, pmFinal 114] := by
    rw [hSm, hgV, hiEq, hwV, hComm]
    rw [← hPm0, ← hPm1, ← hPm2, ← hPm3, ← hPm4]
  have hValueL : smFinal 4 = allGatherPrimDimN 1 [pmFinal 110, pmFinal 111, pmFinal 112, pmFinal 113, pmFinal 114].length 0 [pmFinal 110, pmFinal 111, pmFinal 112, pmFinal 113, pmFinal 114] := by
    simpa only [List.length_cons, List.length_nil] using hValue
  have hFullShape : (smFinal 4).shape = [17, 55] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hout : fact_o.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 4) [pmFinal 110, pmFinal 111, pmFinal 112, pmFinal 113, pmFinal 114] 1 [17, 55] [17, 11]
    refine {
      full_value := hValueL
      full_shape := hFullShape
      shards_nonempty := by simp
      gather_dim_lt := by native_decide
      shard_shapes := ?_
      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
    }
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact houtShape0
    · exact houtShape1
    · exact houtShape2
    · exact houtShape3
    · exact houtShape4
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate BWHiddenGraphK5B2S3V17D11.sm BWHiddenGraphK5B2S3V17D11.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWHiddenK5B2S3V17D11
