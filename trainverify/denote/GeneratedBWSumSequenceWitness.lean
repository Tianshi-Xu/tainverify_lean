import denote.RelationCompiler
import denote.KRankBWSumSequence
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSumSequenceCase0
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }] }
def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }, { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }] }
def fact_g : RelationFact := .reduction 900 [900] [1]
def fact_x : RelationFact := .sharded 100 [1000, 1001] 1 [1, 16, 256] [1, 8, 256]
def fact_out : RelationFact := .sharded 200 [2000, 2001] 1 [1, 16, 256] [1, 8, 256]
def state_000000 : RelationState where
  facts := [fact_g, fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }, { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }]
@[irreducible] private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase0.smGraph) store
@[irreducible] private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 200 = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase0.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = bw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.smGraph) smStore 900) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } 200
      (fun t => bw_sum (t 900) (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase0.smGraph t 0 900 100 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.smGraph) smStore 900 = (segment_000000_sm_final smStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } :: (segment_000000_sm_nodes.drop 1)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = bw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.smGraph) smStore 900) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.smGraph) smStore 100) := hout_prefix
      _ = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2000 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = bw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } 2000
      (fun t => bw_sum (t 900) (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase0.pmGraph t 0 900 1000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } :: (segment_000000_pm_nodes.drop 1)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 1000) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2001 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } 2001
      (fun t => bw_sum (t 900) (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase0.pmGraph t 1 900 1001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } :: (segment_000000_pm_nodes.drop 2)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase0.pmGraph) pmStore 1001) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
    let smFinal := segment_000000_sm_final smStore
    let pmFinal := segment_000000_pm_final pmStore
    have hframe : state_000000.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
    have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ReductionRel (smFinal 900) [pmFinal 900]
      [1] at hg
    have hgValue : smFinal 900 = pmFinal 900 :=
      ReductionRel.singleton_value hg
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001] 1 [1, 16, 256] [1, 8, 256] at hx
    have hxValue : smFinal 100 =
        allGatherPrimDimN 1 2 0 [pmFinal 1000, pmFinal 1001] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 200 =
        bw_sum (smFinal 900) (smFinal 100) := by
      exact segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 2000 =
        bw_sum (pmFinal 900) (pmFinal 1000) := by
      exact segment_000000_hPmWriter0 pmStore
    have hXShape0 := hx.shard_shapes (pmFinal 1000) (by simp)
    have hPmWriter1 : pmFinal 2001 =
        bw_sum (pmFinal 900) (pmFinal 1001) := by
      exact segment_000000_hPmWriter1 pmStore
    have hXShape1 := hx.shard_shapes (pmFinal 1001) (by simp)
    have hcomm : bw_sum (smFinal 900)
        (allGatherPrimDimN 1 2 0 [pmFinal 1000, pmFinal 1001]) =
        allGatherPrimDimN 1 2 0 [bw_sum (smFinal 900) (pmFinal 1000), bw_sum (smFinal 900) (pmFinal 1001)] := by
      simpa only [List.length_cons, List.length_nil, List.map] using
        (TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim1_rank3
          (smFinal 900) [pmFinal 1000, pmFinal 1001] 1 8 256
          hx.shards_nonempty (by decide) (by decide) (by decide) hx.shard_shapes)
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001] 1 [1, 16, 256] [1, 8, 256]
      constructor
      · change smFinal 200 = allGatherPrimDimN 1 2 0 [pmFinal 2000, pmFinal 2001]
        rw [hSmWriter, hxValue, hcomm, hgValue]
        rw [← hPmWriter0, ← hPmWriter1]
      · rw [hSmWriter, bw_sum_shape, hx.full_shape]
      · simp
      · exact hx.gather_dim_lt
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1
        · subst shard
          rw [hPmWriter0, bw_sum_shape, hXShape0]
        · subst shard
          rw [hPmWriter1, bw_sum_shape, hXShape1]
      · exact hx.shape_contract
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fact_out] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

private def segment_000000 :
    ClosedDepSegmentCertificate BWSumSequenceCase0.smGraph BWSumSequenceCase0.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000000_sm_final, segment_000000_pm_final] using segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSumSequenceCase0
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSumSequenceCase1
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }, { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }, { rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] }, { rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] }] }
def fact_g : RelationFact := .reduction 900 [900] [1]
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 1 [1, 16, 256] [1, 4, 256]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 1 [1, 16, 256] [1, 4, 256]
def state_000000 : RelationState where
  facts := [fact_g, fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }, { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }, { rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] }, { rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] }]
@[irreducible] private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase1.smGraph) store
@[irreducible] private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 200 = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase1.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = bw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.smGraph) smStore 900) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } 200
      (fun t => bw_sum (t 900) (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase1.smGraph t 0 900 100 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.smGraph) smStore 900 = (segment_000000_sm_final smStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } :: (segment_000000_sm_nodes.drop 1)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = bw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.smGraph) smStore 900) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.smGraph) smStore 100) := hout_prefix
      _ = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2000 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = bw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } 2000
      (fun t => bw_sum (t 900) (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase1.pmGraph t 0 900 1000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } :: (segment_000000_pm_nodes.drop 1)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1000) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2001 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } 2001
      (fun t => bw_sum (t 900) (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase1.pmGraph t 1 900 1001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } :: (segment_000000_pm_nodes.drop 2)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1001) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2002 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = bw_sum (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] } 2002
      (fun t => bw_sum (t 900) (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase1.pmGraph t 2 900 1002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] } :: (segment_000000_pm_nodes.drop 3)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1002) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2003 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1003) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2003 = bw_sum (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] } 2003
      (fun t => bw_sum (t 900) (t 1003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase1.pmGraph t 3 900 1003 2003
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] } :: (segment_000000_pm_nodes.drop 4)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2003 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1003) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase1.pmGraph) pmStore 1003) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1003) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
    let smFinal := segment_000000_sm_final smStore
    let pmFinal := segment_000000_pm_final pmStore
    have hframe : state_000000.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
    have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ReductionRel (smFinal 900) [pmFinal 900]
      [1] at hg
    have hgValue : smFinal 900 = pmFinal 900 :=
      ReductionRel.singleton_value hg
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 1 [1, 16, 256] [1, 4, 256] at hx
    have hxValue : smFinal 100 =
        allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 200 =
        bw_sum (smFinal 900) (smFinal 100) := by
      exact segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 2000 =
        bw_sum (pmFinal 900) (pmFinal 1000) := by
      exact segment_000000_hPmWriter0 pmStore
    have hXShape0 := hx.shard_shapes (pmFinal 1000) (by simp)
    have hPmWriter1 : pmFinal 2001 =
        bw_sum (pmFinal 900) (pmFinal 1001) := by
      exact segment_000000_hPmWriter1 pmStore
    have hXShape1 := hx.shard_shapes (pmFinal 1001) (by simp)
    have hPmWriter2 : pmFinal 2002 =
        bw_sum (pmFinal 900) (pmFinal 1002) := by
      exact segment_000000_hPmWriter2 pmStore
    have hXShape2 := hx.shard_shapes (pmFinal 1002) (by simp)
    have hPmWriter3 : pmFinal 2003 =
        bw_sum (pmFinal 900) (pmFinal 1003) := by
      exact segment_000000_hPmWriter3 pmStore
    have hXShape3 := hx.shard_shapes (pmFinal 1003) (by simp)
    have hcomm : bw_sum (smFinal 900)
        (allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003]) =
        allGatherPrimDimN 1 4 0 [bw_sum (smFinal 900) (pmFinal 1000), bw_sum (smFinal 900) (pmFinal 1001), bw_sum (smFinal 900) (pmFinal 1002), bw_sum (smFinal 900) (pmFinal 1003)] := by
      simpa only [List.length_cons, List.length_nil, List.map] using
        (TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim1_rank3
          (smFinal 900) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 1 4 256
          hx.shards_nonempty (by decide) (by decide) (by decide) hx.shard_shapes)
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 [1, 16, 256] [1, 4, 256]
      constructor
      · change smFinal 200 = allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003]
        rw [hSmWriter, hxValue, hcomm, hgValue]
        rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2, ← hPmWriter3]
      · rw [hSmWriter, bw_sum_shape, hx.full_shape]
      · simp
      · exact hx.gather_dim_lt
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3
        · subst shard
          rw [hPmWriter0, bw_sum_shape, hXShape0]
        · subst shard
          rw [hPmWriter1, bw_sum_shape, hXShape1]
        · subst shard
          rw [hPmWriter2, bw_sum_shape, hXShape2]
        · subst shard
          rw [hPmWriter3, bw_sum_shape, hXShape3]
      · exact hx.shape_contract
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fact_out] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

private def segment_000000 :
    ClosedDepSegmentCertificate BWSumSequenceCase1.smGraph BWSumSequenceCase1.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000000_sm_final, segment_000000_pm_final] using segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSumSequenceCase1
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSumSequenceCase2
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }, { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }, { rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] }] }
def fact_g : RelationFact := .reduction 900 [900] [1]
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 15, 7] [2, 5, 7]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002] 1 [2, 15, 7] [2, 5, 7]
def state_000000 : RelationState where
  facts := [fact_g, fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }, { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }, { rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] }]
@[irreducible] private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase2.smGraph) store
@[irreducible] private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 200 = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase2.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = bw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.smGraph) smStore 900) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } 200
      (fun t => bw_sum (t 900) (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase2.smGraph t 0 900 100 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.smGraph) smStore 900 = (segment_000000_sm_final smStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } :: (segment_000000_sm_nodes.drop 1)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = bw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.smGraph) smStore 900) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.smGraph) smStore 100) := hout_prefix
      _ = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2000 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = bw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } 2000
      (fun t => bw_sum (t 900) (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase2.pmGraph t 0 900 1000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } :: (segment_000000_pm_nodes.drop 1)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 1000) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2001 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } 2001
      (fun t => bw_sum (t 900) (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase2.pmGraph t 1 900 1001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } :: (segment_000000_pm_nodes.drop 2)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 1001) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2002 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = bw_sum (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] } 2002
      (fun t => bw_sum (t 900) (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase2.pmGraph t 2 900 1002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] } :: (segment_000000_pm_nodes.drop 3)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase2.pmGraph) pmStore 1002) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
    let smFinal := segment_000000_sm_final smStore
    let pmFinal := segment_000000_pm_final pmStore
    have hframe : state_000000.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
    have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ReductionRel (smFinal 900) [pmFinal 900]
      [1] at hg
    have hgValue : smFinal 900 = pmFinal 900 :=
      ReductionRel.singleton_value hg
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 1 [2, 15, 7] [2, 5, 7] at hx
    have hxValue : smFinal 100 =
        allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 200 =
        bw_sum (smFinal 900) (smFinal 100) := by
      exact segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 2000 =
        bw_sum (pmFinal 900) (pmFinal 1000) := by
      exact segment_000000_hPmWriter0 pmStore
    have hXShape0 := hx.shard_shapes (pmFinal 1000) (by simp)
    have hPmWriter1 : pmFinal 2001 =
        bw_sum (pmFinal 900) (pmFinal 1001) := by
      exact segment_000000_hPmWriter1 pmStore
    have hXShape1 := hx.shard_shapes (pmFinal 1001) (by simp)
    have hPmWriter2 : pmFinal 2002 =
        bw_sum (pmFinal 900) (pmFinal 1002) := by
      exact segment_000000_hPmWriter2 pmStore
    have hXShape2 := hx.shard_shapes (pmFinal 1002) (by simp)
    have hcomm : bw_sum (smFinal 900)
        (allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002]) =
        allGatherPrimDimN 1 3 0 [bw_sum (smFinal 900) (pmFinal 1000), bw_sum (smFinal 900) (pmFinal 1001), bw_sum (smFinal 900) (pmFinal 1002)] := by
      simpa only [List.length_cons, List.length_nil, List.map] using
        (TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim1_rank3
          (smFinal 900) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 2 5 7
          hx.shards_nonempty (by decide) (by decide) (by decide) hx.shard_shapes)
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 1 [2, 15, 7] [2, 5, 7]
      constructor
      · change smFinal 200 = allGatherPrimDimN 1 3 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002]
        rw [hSmWriter, hxValue, hcomm, hgValue]
        rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
      · rw [hSmWriter, bw_sum_shape, hx.full_shape]
      · simp
      · exact hx.gather_dim_lt
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst shard
          rw [hPmWriter0, bw_sum_shape, hXShape0]
        · subst shard
          rw [hPmWriter1, bw_sum_shape, hXShape1]
        · subst shard
          rw [hPmWriter2, bw_sum_shape, hXShape2]
      · exact hx.shape_contract
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fact_out] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

private def segment_000000 :
    ClosedDepSegmentCertificate BWSumSequenceCase2.smGraph BWSumSequenceCase2.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000000_sm_final, segment_000000_pm_final] using segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSumSequenceCase2
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSumSequenceCase3
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }] }
def pmGraph : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }, { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }, { rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] }, { rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] }, { rank := 4, op := "OpName.BW_sum", ins := [900, 1004], outs := [2004] }] }
def fact_g : RelationFact := .reduction 900 [900] [1]
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002, 1003, 1004] 1 [3, 5, 2] [3, 1, 2]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002, 2003, 2004] 1 [3, 5, 2] [3, 1, 2]
def state_000000 : RelationState where
  facts := [fact_g, fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }, { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }, { rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] }, { rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] }, { rank := 4, op := "OpName.BW_sum", ins := [900, 1004], outs := [2004] }]
@[irreducible] private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase3.smGraph) store
@[irreducible] private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 200 = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase3.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = bw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.smGraph) smStore 900) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } 200
      (fun t => bw_sum (t 900) (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase3.smGraph t 0 900 100 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.smGraph) smStore 900 = (segment_000000_sm_final smStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } :: (segment_000000_sm_nodes.drop 1)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 100], outs := [200] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = bw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.smGraph) smStore 900) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.smGraph) smStore 100) := hout_prefix
      _ = bw_sum ((segment_000000_sm_final smStore) 900) ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2000 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = bw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } 2000
      (fun t => bw_sum (t 900) (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase3.pmGraph t 0 900 1000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } :: (segment_000000_pm_nodes.drop 1)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_sum", ins := [900, 1000], outs := [2000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1000) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2001 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } 2001
      (fun t => bw_sum (t 900) (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase3.pmGraph t 1 900 1001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } :: (segment_000000_pm_nodes.drop 2)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_sum", ins := [900, 1001], outs := [2001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1001) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2002 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = bw_sum (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] } 2002
      (fun t => bw_sum (t 900) (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase3.pmGraph t 2 900 1002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] } :: (segment_000000_pm_nodes.drop 3)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_sum", ins := [900, 1002], outs := [2002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1002) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2003 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1003) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2003 = bw_sum (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] } 2003
      (fun t => bw_sum (t 900) (t 1003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase3.pmGraph t 3 900 1003 2003
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] } :: (segment_000000_pm_nodes.drop 4)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_sum", ins := [900, 1003], outs := [2003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2003 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1003) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1003) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1003) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter4 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2004 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1004) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 4, op := "OpName.BW_sum", ins := [900, 1004], outs := [2004] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2004 = bw_sum (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1004) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 4, op := "OpName.BW_sum", ins := [900, 1004], outs := [2004] } 2004
      (fun t => bw_sum (t 900) (t 1004)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out BWSumSequenceCase3.pmGraph t 4 900 1004 2004
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900 = (segment_000000_pm_final pmStore) 900 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_sum", ins := [900, 1004], outs := [2004] } :: (segment_000000_pm_nodes.drop 5)) 900
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1004 = (segment_000000_pm_final pmStore) 1004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSumSequenceCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_sum", ins := [900, 1004], outs := [2004] } :: (segment_000000_pm_nodes.drop 5)) 1004
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2004 = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1004) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 900) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSumSequenceCase3.pmGraph) pmStore 1004) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 900) ((segment_000000_pm_final pmStore) 1004) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
    let smFinal := segment_000000_sm_final smStore
    let pmFinal := segment_000000_pm_final pmStore
    have hframe : state_000000.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
    have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ReductionRel (smFinal 900) [pmFinal 900]
      [1] at hg
    have hgValue : smFinal 900 = pmFinal 900 :=
      ReductionRel.singleton_value hg
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] 1 [3, 5, 2] [3, 1, 2] at hx
    have hxValue : smFinal 100 =
        allGatherPrimDimN 1 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 200 =
        bw_sum (smFinal 900) (smFinal 100) := by
      exact segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 2000 =
        bw_sum (pmFinal 900) (pmFinal 1000) := by
      exact segment_000000_hPmWriter0 pmStore
    have hXShape0 := hx.shard_shapes (pmFinal 1000) (by simp)
    have hPmWriter1 : pmFinal 2001 =
        bw_sum (pmFinal 900) (pmFinal 1001) := by
      exact segment_000000_hPmWriter1 pmStore
    have hXShape1 := hx.shard_shapes (pmFinal 1001) (by simp)
    have hPmWriter2 : pmFinal 2002 =
        bw_sum (pmFinal 900) (pmFinal 1002) := by
      exact segment_000000_hPmWriter2 pmStore
    have hXShape2 := hx.shard_shapes (pmFinal 1002) (by simp)
    have hPmWriter3 : pmFinal 2003 =
        bw_sum (pmFinal 900) (pmFinal 1003) := by
      exact segment_000000_hPmWriter3 pmStore
    have hXShape3 := hx.shard_shapes (pmFinal 1003) (by simp)
    have hPmWriter4 : pmFinal 2004 =
        bw_sum (pmFinal 900) (pmFinal 1004) := by
      exact segment_000000_hPmWriter4 pmStore
    have hXShape4 := hx.shard_shapes (pmFinal 1004) (by simp)
    have hcomm : bw_sum (smFinal 900)
        (allGatherPrimDimN 1 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004]) =
        allGatherPrimDimN 1 5 0 [bw_sum (smFinal 900) (pmFinal 1000), bw_sum (smFinal 900) (pmFinal 1001), bw_sum (smFinal 900) (pmFinal 1002), bw_sum (smFinal 900) (pmFinal 1003), bw_sum (smFinal 900) (pmFinal 1004)] := by
      simpa only [List.length_cons, List.length_nil, List.map] using
        (TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim1_rank3
          (smFinal 900) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] 3 1 2
          hx.shards_nonempty (by decide) (by decide) (by decide) hx.shard_shapes)
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] 1 [3, 5, 2] [3, 1, 2]
      constructor
      · change smFinal 200 = allGatherPrimDimN 1 5 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004]
        rw [hSmWriter, hxValue, hcomm, hgValue]
        rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2, ← hPmWriter3, ← hPmWriter4]
      · rw [hSmWriter, bw_sum_shape, hx.full_shape]
      · simp
      · exact hx.gather_dim_lt
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3 | h4
        · subst shard
          rw [hPmWriter0, bw_sum_shape, hXShape0]
        · subst shard
          rw [hPmWriter1, bw_sum_shape, hXShape1]
        · subst shard
          rw [hPmWriter2, bw_sum_shape, hXShape2]
        · subst shard
          rw [hPmWriter3, bw_sum_shape, hXShape3]
        · subst shard
          rw [hPmWriter4, bw_sum_shape, hXShape4]
      · exact hx.shape_contract
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fact_out] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

private def segment_000000 :
    ClosedDepSegmentCertificate BWSumSequenceCase3.smGraph BWSumSequenceCase3.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000000_sm_final, segment_000000_pm_final] using segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSumSequenceCase3
