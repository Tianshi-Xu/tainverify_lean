import denote.RelationCompiler
import denote.KRankBWLinearDxSequence
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLinearDxCase0
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001] 1 [1, 16, 64] [1, 8, 64]
def fact_x : RelationFact := .sharded 200 [2000, 2001] 1 [1, 16, 64] [1, 8, 64]
def fact_w : RelationFact := .sharded 300 [300] 0 [64, 64] [64, 64]
def fact_out : RelationFact := .sharded 400 [4000, 4001] 1 [1, 16, 64] [1, 8, 64]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) s

private theorem segment_000000_hSmWriter (store : Store) : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 400 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase0.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase0.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase0.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase0.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store 300 = (segment_000000_sm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase0.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.smGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (store : Store) : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase0.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase0.pmGraph t 0 1000 2000 300 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase0.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase0.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase0.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (store : Store) : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase0.pmGraph store
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1001) (t 2001) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase0.pmGraph t 1 1001 2001 300 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase0.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 2001 = (segment_000000_pm_final store) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase0.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase0.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase0.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_before.Holds smStore pmStore) : state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
 let smFinal := segment_000000_sm_final smStore
 let pmFinal := segment_000000_pm_final pmStore
 have hframe : state_before.Holds smFinal pmFinal := by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final; apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
 have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001] 1 [1, 16, 64] [1, 8, 64] at hg
 have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001] 1 [1, 16, 64] [1, 8, 64] at hx
 have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 300) [pmFinal 300] 0 [64, 64] [64, 64] at hw
 have hwEq : smFinal 300 = pmFinal 300 := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)]; decide)
 have hgV : smFinal 100 = allGatherPrimDimN 1 2 0 [pmFinal 1000, pmFinal 1001] := by simpa only [List.length_cons,List.length_nil] using hg.full_value
 have hS : smFinal 400 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).1 := segment_000000_hSmWriter smStore
 have hP0 : pmFinal 4000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1 := segment_000000_hPmWriter0 pmStore
 have hP1 : pmFinal 4001 = (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1 := segment_000000_hPmWriter1 pmStore
 have hcomm := TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 2 1 8 64 64 [pmFinal 1000, pmFinal 1001] [pmFinal 2000, pmFinal 2001] (smFinal 200) (pmFinal 300)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes hx.full_shape (hw.shard_shapes _ (by simp))
 have hcommExplicit : (bw_linear (allGatherPrimDimN 1 2 0 [pmFinal 1000, pmFinal 1001]) (smFinal 200) (pmFinal 300)).1 = allGatherPrimDimN 1 2 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1, (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1] := by simpa only [List.zipWith] using hcomm
 have hV : smFinal 400 = allGatherPrimDimN 1 2 0 [pmFinal 4000, pmFinal 4001] := by
   rw [hS, hgV, hwEq, hcommExplicit]
   rw [← hP0, ← hP1]
 have hFull : (smFinal 400).shape = [1, 16, 64] := by rw [hS]; exact bw_linear_3d_fst_shape 1 16 64 64 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape0 : (pmFinal 4000).shape = [1, 8, 64] := by rw [hP0]; exact bw_linear_3d_fst_shape 1 8 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1 : (pmFinal 4001).shape = [1, 8, 64] := by rw [hP1]; exact bw_linear_3d_fst_shape 1 8 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout : fact_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001] 1 [1, 16, 64] [1, 8, 64]
   refine { full_value := ?_, full_shape := hFull, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simpa only [List.length_cons,List.length_nil] using hV
   · simp only [List.forall_mem_cons]; exact ⟨hShape0, hShape1, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 intro fact hfact
 have hc : fact ∈ [fact_out] ++ state_before.facts := (show state_after.facts ⊆ [fact_out] ++ state_before.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh | old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh; subst fact; exact hout
 · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticBWLinearDxCase0.smGraph SyntheticBWLinearDxCase0.pmGraph state_before state_after where
 smNodes := segment_000000_sm_nodes
 pmNodes := segment_000000_pm_nodes
 sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000
end
end SyntheticBWLinearDxCase0
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLinearDxCase1
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 1 [1, 16, 64] [1, 4, 64]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 1 [1, 16, 64] [1, 4, 64]
def fact_w : RelationFact := .sharded 300 [300] 0 [64, 64] [64, 64]
def fact_out : RelationFact := .sharded 400 [4000, 4001, 4002, 4003] 1 [1, 16, 64] [1, 4, 64]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) s

private theorem segment_000000_hSmWriter (store : Store) : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 400 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase1.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase1.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store 300 = (segment_000000_sm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.smGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (store : Store) : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase1.pmGraph t 0 1000 2000 300 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (store : Store) : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1001) (t 2001) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase1.pmGraph t 1 1001 2001 300 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2001 = (segment_000000_pm_final store) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (store : Store) : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4002 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } 4002
      (fun t => (bw_linear (t 1002) (t 2002) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase1.pmGraph t 2 1002 2002 300 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1002 = (segment_000000_pm_final store) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2002 = (segment_000000_pm_final store) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter3 (store : Store) : (segment_000000_pm_final store) 4003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4003 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } 4003
      (fun t => (bw_linear (t 1003) (t 2003) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase1.pmGraph t 3 1003 2003 300 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1003 = (segment_000000_pm_final store) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2003 = (segment_000000_pm_final store) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase1.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase1.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_before.Holds smStore pmStore) : state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
 let smFinal := segment_000000_sm_final smStore
 let pmFinal := segment_000000_pm_final pmStore
 have hframe : state_before.Holds smFinal pmFinal := by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final; apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
 have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 1 [1, 16, 64] [1, 4, 64] at hg
 have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 [1, 16, 64] [1, 4, 64] at hx
 have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 300) [pmFinal 300] 0 [64, 64] [64, 64] at hw
 have hwEq : smFinal 300 = pmFinal 300 := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)]; decide)
 have hgV : smFinal 100 = allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] := by simpa only [List.length_cons,List.length_nil] using hg.full_value
 have hS : smFinal 400 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).1 := segment_000000_hSmWriter smStore
 have hP0 : pmFinal 4000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1 := segment_000000_hPmWriter0 pmStore
 have hP1 : pmFinal 4001 = (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1 := segment_000000_hPmWriter1 pmStore
 have hP2 : pmFinal 4002 = (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 300)).1 := segment_000000_hPmWriter2 pmStore
 have hP3 : pmFinal 4003 = (bw_linear (pmFinal 1003) (pmFinal 2003) (pmFinal 300)).1 := segment_000000_hPmWriter3 pmStore
 have hcomm := TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 4 1 4 64 64 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] (smFinal 200) (pmFinal 300)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes hx.full_shape (hw.shard_shapes _ (by simp))
 have hcommExplicit : (bw_linear (allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003]) (smFinal 200) (pmFinal 300)).1 = allGatherPrimDimN 1 4 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1, (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1, (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 300)).1, (bw_linear (pmFinal 1003) (pmFinal 2003) (pmFinal 300)).1] := by simpa only [List.zipWith] using hcomm
 have hV : smFinal 400 = allGatherPrimDimN 1 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] := by
   rw [hS, hgV, hwEq, hcommExplicit]
   rw [← hP0, ← hP1, ← hP2, ← hP3]
 have hFull : (smFinal 400).shape = [1, 16, 64] := by rw [hS]; exact bw_linear_3d_fst_shape 1 16 64 64 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape0 : (pmFinal 4000).shape = [1, 4, 64] := by rw [hP0]; exact bw_linear_3d_fst_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1 : (pmFinal 4001).shape = [1, 4, 64] := by rw [hP1]; exact bw_linear_3d_fst_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape2 : (pmFinal 4002).shape = [1, 4, 64] := by rw [hP2]; exact bw_linear_3d_fst_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape3 : (pmFinal 4003).shape = [1, 4, 64] := by rw [hP3]; exact bw_linear_3d_fst_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout : fact_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 1 [1, 16, 64] [1, 4, 64]
   refine { full_value := ?_, full_shape := hFull, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simpa only [List.length_cons,List.length_nil] using hV
   · simp only [List.forall_mem_cons]; exact ⟨hShape0, hShape1, hShape2, hShape3, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 intro fact hfact
 have hc : fact ∈ [fact_out] ++ state_before.facts := (show state_after.facts ⊆ [fact_out] ++ state_before.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh | old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh; subst fact; exact hout
 · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticBWLinearDxCase1.smGraph SyntheticBWLinearDxCase1.pmGraph state_before state_after where
 smNodes := segment_000000_sm_nodes
 pmNodes := segment_000000_pm_nodes
 sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000
end
end SyntheticBWLinearDxCase1
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLinearDxCase2
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 15, 7] [2, 5, 7]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002] 1 [2, 15, 11] [2, 5, 11]
def fact_w : RelationFact := .sharded 300 [300] 0 [7, 11] [7, 11]
def fact_out : RelationFact := .sharded 400 [4000, 4001, 4002] 1 [2, 15, 11] [2, 5, 11]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) s

private theorem segment_000000_hSmWriter (store : Store) : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 400 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase2.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase2.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store 300 = (segment_000000_sm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.smGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (store : Store) : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase2.pmGraph t 0 1000 2000 300 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (store : Store) : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1001) (t 2001) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase2.pmGraph t 1 1001 2001 300 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 2001 = (segment_000000_pm_final store) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (store : Store) : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4002 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } 4002
      (fun t => (bw_linear (t 1002) (t 2002) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase2.pmGraph t 2 1002 2002 300 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 1002 = (segment_000000_pm_final store) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 2002 = (segment_000000_pm_final store) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase2.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase2.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_before.Holds smStore pmStore) : state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
 let smFinal := segment_000000_sm_final smStore
 let pmFinal := segment_000000_pm_final pmStore
 have hframe : state_before.Holds smFinal pmFinal := by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final; apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
 have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 1 [2, 15, 7] [2, 5, 7] at hg
 have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 1 [2, 15, 11] [2, 5, 11] at hx
 have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 300) [pmFinal 300] 0 [7, 11] [7, 11] at hw
 have hwEq : smFinal 300 = pmFinal 300 := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)]; decide)
 have hgV : smFinal 100 = allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002] := by simpa only [List.length_cons,List.length_nil] using hg.full_value
 have hS : smFinal 400 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).1 := segment_000000_hSmWriter smStore
 have hP0 : pmFinal 4000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1 := segment_000000_hPmWriter0 pmStore
 have hP1 : pmFinal 4001 = (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1 := segment_000000_hPmWriter1 pmStore
 have hP2 : pmFinal 4002 = (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 300)).1 := segment_000000_hPmWriter2 pmStore
 have hcomm := TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 3 2 5 7 11 [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] (smFinal 200) (pmFinal 300)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes hx.full_shape (hw.shard_shapes _ (by simp))
 have hcommExplicit : (bw_linear (allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002]) (smFinal 200) (pmFinal 300)).1 = allGatherPrimDimN 1 3 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1, (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1, (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 300)).1] := by simpa only [List.zipWith] using hcomm
 have hV : smFinal 400 = allGatherPrimDimN 1 3 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002] := by
   rw [hS, hgV, hwEq, hcommExplicit]
   rw [← hP0, ← hP1, ← hP2]
 have hFull : (smFinal 400).shape = [2, 15, 11] := by rw [hS]; exact bw_linear_3d_fst_shape 2 15 7 11 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape0 : (pmFinal 4000).shape = [2, 5, 11] := by rw [hP0]; exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1 : (pmFinal 4001).shape = [2, 5, 11] := by rw [hP1]; exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape2 : (pmFinal 4002).shape = [2, 5, 11] := by rw [hP2]; exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout : fact_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002] 1 [2, 15, 11] [2, 5, 11]
   refine { full_value := ?_, full_shape := hFull, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simpa only [List.length_cons,List.length_nil] using hV
   · simp only [List.forall_mem_cons]; exact ⟨hShape0, hShape1, hShape2, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 intro fact hfact
 have hc : fact ∈ [fact_out] ++ state_before.facts := (show state_after.facts ⊆ [fact_out] ++ state_before.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh | old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh; subst fact; exact hout
 · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticBWLinearDxCase2.smGraph SyntheticBWLinearDxCase2.pmGraph state_before state_after where
 smNodes := segment_000000_sm_nodes
 pmNodes := segment_000000_pm_nodes
 sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000
end
end SyntheticBWLinearDxCase2
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLinearDxCase3
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }] }
def fact_g : RelationFact := .sharded 100 [1000] 1 [3, 2, 1] [3, 2, 1]
def fact_x : RelationFact := .sharded 200 [2000] 1 [3, 2, 4] [3, 2, 4]
def fact_w : RelationFact := .sharded 300 [300] 0 [1, 4] [1, 4]
def fact_out : RelationFact := .sharded 400 [4000] 1 [3, 2, 4] [3, 2, 4]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) s

private theorem segment_000000_hSmWriter (store : Store) : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 400 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase3.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase3.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase3.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase3.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store 300 = (segment_000000_sm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase3.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.smGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (store : Store) : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase3.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase3.pmGraph t 0 1000 2000 300 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase3.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase3.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase3.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase3.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_before.Holds smStore pmStore) : state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
 let smFinal := segment_000000_sm_final smStore
 let pmFinal := segment_000000_pm_final pmStore
 have hframe : state_before.Holds smFinal pmFinal := by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final; apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
 have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 100) [pmFinal 1000] 1 [3, 2, 1] [3, 2, 1] at hg
 have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 200) [pmFinal 2000] 1 [3, 2, 4] [3, 2, 4] at hx
 have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 300) [pmFinal 300] 0 [1, 4] [1, 4] at hw
 have hwEq : smFinal 300 = pmFinal 300 := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)]; decide)
 have hgV : smFinal 100 = allGatherPrimDimN 1 1 0 [pmFinal 1000] := by simpa only [List.length_cons,List.length_nil] using hg.full_value
 have hS : smFinal 400 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).1 := segment_000000_hSmWriter smStore
 have hP0 : pmFinal 4000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1 := segment_000000_hPmWriter0 pmStore
 have hcomm := TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 1 3 2 1 4 [pmFinal 1000] [pmFinal 2000] (smFinal 200) (pmFinal 300)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes hx.full_shape (hw.shard_shapes _ (by simp))
 have hcommExplicit : (bw_linear (allGatherPrimDimN 1 1 0 [pmFinal 1000]) (smFinal 200) (pmFinal 300)).1 = allGatherPrimDimN 1 1 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1] := by simpa only [List.zipWith] using hcomm
 have hV : smFinal 400 = allGatherPrimDimN 1 1 0 [pmFinal 4000] := by
   rw [hS, hgV, hwEq, hcommExplicit]
   rw [← hP0]
 have hFull : (smFinal 400).shape = [3, 2, 4] := by rw [hS]; exact bw_linear_3d_fst_shape 3 2 1 4 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape0 : (pmFinal 4000).shape = [3, 2, 4] := by rw [hP0]; exact bw_linear_3d_fst_shape 3 2 1 4 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout : fact_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 400) [pmFinal 4000] 1 [3, 2, 4] [3, 2, 4]
   refine { full_value := ?_, full_shape := hFull, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simpa only [List.length_cons,List.length_nil] using hV
   · simp only [List.forall_mem_cons]; exact ⟨hShape0, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 intro fact hfact
 have hc : fact ∈ [fact_out] ++ state_before.facts := (show state_after.facts ⊆ [fact_out] ++ state_before.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh | old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh; subst fact; exact hout
 · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticBWLinearDxCase3.smGraph SyntheticBWLinearDxCase3.pmGraph state_before state_after where
 smNodes := segment_000000_sm_nodes
 pmNodes := segment_000000_pm_nodes
 sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000
end
end SyntheticBWLinearDxCase3
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLinearDxCase4
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_linear", ins := [1004, 2004, 300], outs := [4004, 5004] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003, 1004] 1 [2, 5, 3] [2, 1, 3]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003, 2004] 1 [2, 5, 2] [2, 1, 2]
def fact_w : RelationFact := .sharded 300 [300] 0 [3, 2] [3, 2]
def fact_out : RelationFact := .sharded 400 [4000, 4001, 4002, 4003, 4004] 1 [2, 5, 2] [2, 1, 2]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_linear", ins := [1004, 2004, 300], outs := [4004, 5004] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) s

private theorem segment_000000_hSmWriter (store : Store) : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 400 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase4.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase4.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store 300 = (segment_000000_sm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.smGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (store : Store) : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase4.pmGraph t 0 1000 2000 300 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (store : Store) : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1001) (t 2001) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase4.pmGraph t 1 1001 2001 300 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2001 = (segment_000000_pm_final store) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (store : Store) : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4002 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } 4002
      (fun t => (bw_linear (t 1002) (t 2002) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase4.pmGraph t 2 1002 2002 300 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1002 = (segment_000000_pm_final store) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2002 = (segment_000000_pm_final store) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter3 (store : Store) : (segment_000000_pm_final store) 4003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4003 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } 4003
      (fun t => (bw_linear (t 1003) (t 2003) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase4.pmGraph t 3 1003 2003 300 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1003 = (segment_000000_pm_final store) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2003 = (segment_000000_pm_final store) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter4 (store : Store) : (segment_000000_pm_final store) 4004 = (bw_linear ((segment_000000_pm_final store) 1004) ((segment_000000_pm_final store) 2004) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 4, op := "OpName.BW_linear", ins := [1004, 2004, 300], outs := [4004, 5004] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4004 = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 4, op := "OpName.BW_linear", ins := [1004, 2004, 300], outs := [4004, 5004] } 4004
      (fun t => (bw_linear (t 1004) (t 2004) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase4.pmGraph t 4 1004 2004 300 4004 5004 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1004 = (segment_000000_pm_final store) 1004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_linear", ins := [1004, 2004, 300], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 1004
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2004 = (segment_000000_pm_final store) 2004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_linear", ins := [1004, 2004, 300], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 2004
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase4.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_linear", ins := [1004, 2004, 300], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4004 = (bw_linear ((segment_000000_pm_final store) 1004) ((segment_000000_pm_final store) 2004) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase4.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1004) ((segment_000000_pm_final store) 2004) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_before.Holds smStore pmStore) : state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
 let smFinal := segment_000000_sm_final smStore
 let pmFinal := segment_000000_pm_final pmStore
 have hframe : state_before.Holds smFinal pmFinal := by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final; apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
 have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] 1 [2, 5, 3] [2, 1, 3] at hg
 have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] 1 [2, 5, 2] [2, 1, 2] at hx
 have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 300) [pmFinal 300] 0 [3, 2] [3, 2] at hw
 have hwEq : smFinal 300 = pmFinal 300 := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)]; decide)
 have hgV : smFinal 100 = allGatherPrimDimN 1 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] := by simpa only [List.length_cons,List.length_nil] using hg.full_value
 have hS : smFinal 400 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).1 := segment_000000_hSmWriter smStore
 have hP0 : pmFinal 4000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1 := segment_000000_hPmWriter0 pmStore
 have hP1 : pmFinal 4001 = (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1 := segment_000000_hPmWriter1 pmStore
 have hP2 : pmFinal 4002 = (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 300)).1 := segment_000000_hPmWriter2 pmStore
 have hP3 : pmFinal 4003 = (bw_linear (pmFinal 1003) (pmFinal 2003) (pmFinal 300)).1 := segment_000000_hPmWriter3 pmStore
 have hP4 : pmFinal 4004 = (bw_linear (pmFinal 1004) (pmFinal 2004) (pmFinal 300)).1 := segment_000000_hPmWriter4 pmStore
 have hcomm := TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 5 2 1 3 2 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] (smFinal 200) (pmFinal 300)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes hx.full_shape (hw.shard_shapes _ (by simp))
 have hcommExplicit : (bw_linear (allGatherPrimDimN 1 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004]) (smFinal 200) (pmFinal 300)).1 = allGatherPrimDimN 1 5 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1, (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1, (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 300)).1, (bw_linear (pmFinal 1003) (pmFinal 2003) (pmFinal 300)).1, (bw_linear (pmFinal 1004) (pmFinal 2004) (pmFinal 300)).1] := by simpa only [List.zipWith] using hcomm
 have hV : smFinal 400 = allGatherPrimDimN 1 5 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003, pmFinal 4004] := by
   rw [hS, hgV, hwEq, hcommExplicit]
   rw [← hP0, ← hP1, ← hP2, ← hP3, ← hP4]
 have hFull : (smFinal 400).shape = [2, 5, 2] := by rw [hS]; exact bw_linear_3d_fst_shape 2 5 3 2 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape0 : (pmFinal 4000).shape = [2, 1, 2] := by rw [hP0]; exact bw_linear_3d_fst_shape 2 1 3 2 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1 : (pmFinal 4001).shape = [2, 1, 2] := by rw [hP1]; exact bw_linear_3d_fst_shape 2 1 3 2 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape2 : (pmFinal 4002).shape = [2, 1, 2] := by rw [hP2]; exact bw_linear_3d_fst_shape 2 1 3 2 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape3 : (pmFinal 4003).shape = [2, 1, 2] := by rw [hP3]; exact bw_linear_3d_fst_shape 2 1 3 2 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape4 : (pmFinal 4004).shape = [2, 1, 2] := by rw [hP4]; exact bw_linear_3d_fst_shape 2 1 3 2 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout : fact_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003, pmFinal 4004] 1 [2, 5, 2] [2, 1, 2]
   refine { full_value := ?_, full_shape := hFull, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simpa only [List.length_cons,List.length_nil] using hV
   · simp only [List.forall_mem_cons]; exact ⟨hShape0, hShape1, hShape2, hShape3, hShape4, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 intro fact hfact
 have hc : fact ∈ [fact_out] ++ state_before.facts := (show state_after.facts ⊆ [fact_out] ++ state_before.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh | old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh; subst fact; exact hout
 · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticBWLinearDxCase4.smGraph SyntheticBWLinearDxCase4.pmGraph state_before state_after where
 smNodes := segment_000000_sm_nodes
 pmNodes := segment_000000_pm_nodes
 sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000
end
end SyntheticBWLinearDxCase4
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLinearDxCase5
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 1 [1, 8, 32] [1, 2, 32]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 1 [1, 8, 32] [1, 2, 32]
def fact_w : RelationFact := .sharded 300 [300] 0 [32, 32] [32, 32]
def fact_out : RelationFact := .sharded 400 [4000, 4001, 4002, 4003] 1 [1, 8, 32] [1, 2, 32]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) s

private theorem segment_000000_hSmWriter (store : Store) : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 400 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase5.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase5.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store 300 = (segment_000000_sm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.smGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (store : Store) : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase5.pmGraph t 0 1000 2000 300 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 300], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (store : Store) : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1001) (t 2001) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase5.pmGraph t 1 1001 2001 300 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2001 = (segment_000000_pm_final store) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 300], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (store : Store) : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4002 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } 4002
      (fun t => (bw_linear (t 1002) (t 2002) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase5.pmGraph t 2 1002 2002 300 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1002 = (segment_000000_pm_final store) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2002 = (segment_000000_pm_final store) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 300], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter3 (store : Store) : (segment_000000_pm_final store) 4003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 300)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4003 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } 4003
      (fun t => (bw_linear (t 1003) (t 2003) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxCase5.pmGraph t 3 1003 2003 300 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1003 = (segment_000000_pm_final store) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2003 = (segment_000000_pm_final store) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300 = (segment_000000_pm_final store) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxCase5.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 300], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxCase5.pmGraph) store 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_before.Holds smStore pmStore) : state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
 let smFinal := segment_000000_sm_final smStore
 let pmFinal := segment_000000_pm_final pmStore
 have hframe : state_before.Holds smFinal pmFinal := by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final; apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
 have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 1 [1, 8, 32] [1, 2, 32] at hg
 have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 [1, 8, 32] [1, 2, 32] at hx
 have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 300) [pmFinal 300] 0 [32, 32] [32, 32] at hw
 have hwEq : smFinal 300 = pmFinal 300 := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)]; decide)
 have hgV : smFinal 100 = allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] := by simpa only [List.length_cons,List.length_nil] using hg.full_value
 have hS : smFinal 400 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).1 := segment_000000_hSmWriter smStore
 have hP0 : pmFinal 4000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1 := segment_000000_hPmWriter0 pmStore
 have hP1 : pmFinal 4001 = (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1 := segment_000000_hPmWriter1 pmStore
 have hP2 : pmFinal 4002 = (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 300)).1 := segment_000000_hPmWriter2 pmStore
 have hP3 : pmFinal 4003 = (bw_linear (pmFinal 1003) (pmFinal 2003) (pmFinal 300)).1 := segment_000000_hPmWriter3 pmStore
 have hcomm := TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 4 1 2 32 32 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] (smFinal 200) (pmFinal 300)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes hx.full_shape (hw.shard_shapes _ (by simp))
 have hcommExplicit : (bw_linear (allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003]) (smFinal 200) (pmFinal 300)).1 = allGatherPrimDimN 1 4 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 300)).1, (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 300)).1, (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 300)).1, (bw_linear (pmFinal 1003) (pmFinal 2003) (pmFinal 300)).1] := by simpa only [List.zipWith] using hcomm
 have hV : smFinal 400 = allGatherPrimDimN 1 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] := by
   rw [hS, hgV, hwEq, hcommExplicit]
   rw [← hP0, ← hP1, ← hP2, ← hP3]
 have hFull : (smFinal 400).shape = [1, 8, 32] := by rw [hS]; exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape0 : (pmFinal 4000).shape = [1, 2, 32] := by rw [hP0]; exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1 : (pmFinal 4001).shape = [1, 2, 32] := by rw [hP1]; exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape2 : (pmFinal 4002).shape = [1, 2, 32] := by rw [hP2]; exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape3 : (pmFinal 4003).shape = [1, 2, 32] := by rw [hP3]; exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout : fact_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 1 [1, 8, 32] [1, 2, 32]
   refine { full_value := ?_, full_shape := hFull, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simpa only [List.length_cons,List.length_nil] using hV
   · simp only [List.forall_mem_cons]; exact ⟨hShape0, hShape1, hShape2, hShape3, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 intro fact hfact
 have hc : fact ∈ [fact_out] ++ state_before.facts := (show state_after.facts ⊆ [fact_out] ++ state_before.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh | old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh; subst fact; exact hout
 · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticBWLinearDxCase5.smGraph SyntheticBWLinearDxCase5.pmGraph state_before state_after where
 smNodes := segment_000000_sm_nodes
 pmNodes := segment_000000_pm_nodes
 sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000
end
end SyntheticBWLinearDxCase5