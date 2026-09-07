import denote.RelationCompiler
import denote.KRankBWSoftmaxGeneral
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSoftmaxA1Case0
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] }
def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }] }
def fg : RelationFact := .sharded 100 [1000, 1001] 1 [1, 8, 8, 8] [1, 4, 8, 8]
def fx : RelationFact := .sharded 200 [2000, 2001] 1 [1, 8, 8, 8] [1, 4, 8, 8]
def fo : RelationFact := .sharded 300 [3000, 3001] 1 [1, 8, 8, 8] [1, 4, 8, 8]
def state_000000 : RelationState where
  facts := [fg, fx]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fg, fx, fo]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.smGraph) smStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case0.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } 300
      (fun t => bw_softmax (t 100) (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case0.smGraph t 0 100 200 300 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case0.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case0.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
    calc
      _ = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.smGraph) smStore 200) := hout_prefix
      _ = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 2000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } 3000
      (fun t => bw_softmax (t 1000) (t 2000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case0.pmGraph t 0 1000 2000 3000 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 2000) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3001 = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 2001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } 3001
      (fun t => bw_softmax (t 1001) (t 2001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case0.pmGraph t 1 1001 2001 3001 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 2001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case0.pmGraph) pmStore 2001) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by rw [hout_read_0, hout_read_1]
  exact hout

set_option maxHeartbeats 500000 in
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
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001] 1 [1, 8, 8, 8] [1, 4, 8, 8] at hg
    have hx : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001] 1 [1, 8, 8, 8] [1, 4, 8, 8] at hx
    have hgValue : smFinal 100 = allGatherPrimDimN 1 2 0 [pmFinal 1000, pmFinal 1001] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hxValue : smFinal 200 = allGatherPrimDimN 1 2 0 [pmFinal 2000, pmFinal 2001] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 300 = bw_softmax (smFinal 100) (smFinal 200) :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 3000 = bw_softmax (pmFinal 1000) (pmFinal 2000) :=
      segment_000000_hPmWriter0 pmStore
    have hOutShape0 : (pmFinal 3000).shape = [1, 4, 8, 8] := by
      rw [hPmWriter0]
      exact bw_softmax_shape_g199 _ _ [1, 4, 8] 8 (hx.shard_shapes _ (by simp))
    have hPmWriter1 : pmFinal 3001 = bw_softmax (pmFinal 1001) (pmFinal 2001) :=
      segment_000000_hPmWriter1 pmStore
    have hOutShape1 : (pmFinal 3001).shape = [1, 4, 8, 8] := by
      rw [hPmWriter1]
      exact bw_softmax_shape_g199 _ _ [1, 4, 8] 8 (hx.shard_shapes _ (by simp))
    have hcomm := TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim1_rank4 [pmFinal 1000, pmFinal 1001] [pmFinal 2000, pmFinal 2001] 2 1 4 8 8
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp) (by simp) hg.shard_shapes hx.shard_shapes
    have hOutValue : smFinal 300 = allGatherPrimDimN 1 2 0 [pmFinal 3000, pmFinal 3001] := by
      rw [hSmWriter, hgValue, hxValue, hcomm]
      simp only [List.zipWith]
      rw [← hPmWriter0, ← hPmWriter1]
    have hOutValueList : smFinal 300 = allGatherPrimDimN 1 [pmFinal 3000, pmFinal 3001].length 0 [pmFinal 3000, pmFinal 3001] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 300).shape = [1, 8, 8, 8] := by
      rw [hSmWriter]
      exact bw_softmax_shape_g199 _ _ [1, 8, 8] 8 hx.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001] 1 [1, 8, 8, 8] [1, 4, 8, 8]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := hx.gather_dim_lt
        shard_shapes := ?_
        shape_contract := by
          simp only [List.length_cons, List.length_nil]
          native_decide
      }
      intro piece hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1
      · subst piece
        exact hOutShape0
      · subst piece
        exact hOutShape1
    intro fact hfact
    have covered : fact ∈ [fo] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fo] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate BWSoftmaxA1Case0.smGraph BWSoftmaxA1Case0.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSoftmaxA1Case0
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSoftmaxA1Case1
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }, { rank := 2, op := "OpName.FW_contiguous", ins := [8002], outs := [9002] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }] }
def fg : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 9, 5, 7] [2, 3, 5, 7]
def fx : RelationFact := .sharded 200 [2000, 2001, 2002] 1 [2, 9, 5, 7] [2, 3, 5, 7]
def fo : RelationFact := .sharded 300 [3000, 3001, 3002] 1 [2, 9, 5, 7] [2, 3, 5, 7]
def state_000000 : RelationState where
  facts := [fg, fx]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fg, fx, fo]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }, { rank := 2, op := "OpName.FW_contiguous", ins := [8002], outs := [9002] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.smGraph) smStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case1.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } 300
      (fun t => bw_softmax (t 100) (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case1.smGraph t 0 100 200 300 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case1.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case1.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
    calc
      _ = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.smGraph) smStore 200) := hout_prefix
      _ = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 2000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } 3000
      (fun t => bw_softmax (t 1000) (t 2000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case1.pmGraph t 0 1000 2000 3000 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 2000) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3001 = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 2001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } 3001
      (fun t => bw_softmax (t 1001) (t 2001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case1.pmGraph t 1 1001 2001 3001 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 2001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 2001) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3002 = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 2002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } 3002
      (fun t => bw_softmax (t 1002) (t 2002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case1.pmGraph t 2 1002 2002 3002 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 2002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case1.pmGraph) pmStore 2002) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by rw [hout_read_0, hout_read_1]
  exact hout

set_option maxHeartbeats 500000 in
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
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 1 [2, 9, 5, 7] [2, 3, 5, 7] at hg
    have hx : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 1 [2, 9, 5, 7] [2, 3, 5, 7] at hx
    have hgValue : smFinal 100 = allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hxValue : smFinal 200 = allGatherPrimDimN 1 3 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 300 = bw_softmax (smFinal 100) (smFinal 200) :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 3000 = bw_softmax (pmFinal 1000) (pmFinal 2000) :=
      segment_000000_hPmWriter0 pmStore
    have hOutShape0 : (pmFinal 3000).shape = [2, 3, 5, 7] := by
      rw [hPmWriter0]
      exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 (hx.shard_shapes _ (by simp))
    have hPmWriter1 : pmFinal 3001 = bw_softmax (pmFinal 1001) (pmFinal 2001) :=
      segment_000000_hPmWriter1 pmStore
    have hOutShape1 : (pmFinal 3001).shape = [2, 3, 5, 7] := by
      rw [hPmWriter1]
      exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 (hx.shard_shapes _ (by simp))
    have hPmWriter2 : pmFinal 3002 = bw_softmax (pmFinal 1002) (pmFinal 2002) :=
      segment_000000_hPmWriter2 pmStore
    have hOutShape2 : (pmFinal 3002).shape = [2, 3, 5, 7] := by
      rw [hPmWriter2]
      exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 (hx.shard_shapes _ (by simp))
    have hcomm := TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim1_rank4 [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] 3 2 3 5 7
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp) (by simp) hg.shard_shapes hx.shard_shapes
    have hOutValue : smFinal 300 = allGatherPrimDimN 1 3 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002] := by
      rw [hSmWriter, hgValue, hxValue, hcomm]
      simp only [List.zipWith]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
    have hOutValueList : smFinal 300 = allGatherPrimDimN 1 [pmFinal 3000, pmFinal 3001, pmFinal 3002].length 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 300).shape = [2, 9, 5, 7] := by
      rw [hSmWriter]
      exact bw_softmax_shape_g199 _ _ [2, 9, 5] 7 hx.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002] 1 [2, 9, 5, 7] [2, 3, 5, 7]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := hx.gather_dim_lt
        shard_shapes := ?_
        shape_contract := by
          simp only [List.length_cons, List.length_nil]
          native_decide
      }
      intro piece hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2
      · subst piece
        exact hOutShape0
      · subst piece
        exact hOutShape1
      · subst piece
        exact hOutShape2
    intro fact hfact
    have covered : fact ∈ [fo] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fo] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate BWSoftmaxA1Case1.smGraph BWSoftmaxA1Case1.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSoftmaxA1Case1
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSoftmaxA1Case2
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }, { rank := 2, op := "OpName.FW_contiguous", ins := [8002], outs := [9002] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }, { rank := 3, op := "OpName.FW_contiguous", ins := [8003], outs := [9003] }, { rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] }] }
def fg : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 1 [3, 8, 4, 6] [3, 2, 4, 6]
def fx : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 1 [3, 8, 4, 6] [3, 2, 4, 6]
def fo : RelationFact := .sharded 300 [3000, 3001, 3002, 3003] 1 [3, 8, 4, 6] [3, 2, 4, 6]
def state_000000 : RelationState where
  facts := [fg, fx]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fg, fx, fo]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }, { rank := 2, op := "OpName.FW_contiguous", ins := [8002], outs := [9002] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }, { rank := 3, op := "OpName.FW_contiguous", ins := [8003], outs := [9003] }, { rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.smGraph) smStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case2.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } 300
      (fun t => bw_softmax (t 100) (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case2.smGraph t 0 100 200 300 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
    calc
      _ = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.smGraph) smStore 200) := hout_prefix
      _ = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } 3000
      (fun t => bw_softmax (t 1000) (t 2000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case2.pmGraph t 0 1000 2000 3000 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2000) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3001 = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } 3001
      (fun t => bw_softmax (t 1001) (t 2001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case2.pmGraph t 1 1001 2001 3001 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 2001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2001) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3002 = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } 3002
      (fun t => bw_softmax (t 1002) (t 2002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case2.pmGraph t 2 1002 2002 3002 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 2002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2002) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3003 = bw_softmax ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3003 = bw_softmax (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] } 3003
      (fun t => bw_softmax (t 1003) (t 2003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA1Case2.pmGraph t 3 1003 2003 3003 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] } :: (segment_000000_pm_nodes.drop 8)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] } :: (segment_000000_pm_nodes.drop 8)) 2003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3003 = bw_softmax ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA1Case2.pmGraph) pmStore 2003) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) := by rw [hout_read_0, hout_read_1]
  exact hout

set_option maxHeartbeats 500000 in
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
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 1 [3, 8, 4, 6] [3, 2, 4, 6] at hg
    have hx : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 [3, 8, 4, 6] [3, 2, 4, 6] at hx
    have hgValue : smFinal 100 = allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hxValue : smFinal 200 = allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 300 = bw_softmax (smFinal 100) (smFinal 200) :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 3000 = bw_softmax (pmFinal 1000) (pmFinal 2000) :=
      segment_000000_hPmWriter0 pmStore
    have hOutShape0 : (pmFinal 3000).shape = [3, 2, 4, 6] := by
      rw [hPmWriter0]
      exact bw_softmax_shape_g199 _ _ [3, 2, 4] 6 (hx.shard_shapes _ (by simp))
    have hPmWriter1 : pmFinal 3001 = bw_softmax (pmFinal 1001) (pmFinal 2001) :=
      segment_000000_hPmWriter1 pmStore
    have hOutShape1 : (pmFinal 3001).shape = [3, 2, 4, 6] := by
      rw [hPmWriter1]
      exact bw_softmax_shape_g199 _ _ [3, 2, 4] 6 (hx.shard_shapes _ (by simp))
    have hPmWriter2 : pmFinal 3002 = bw_softmax (pmFinal 1002) (pmFinal 2002) :=
      segment_000000_hPmWriter2 pmStore
    have hOutShape2 : (pmFinal 3002).shape = [3, 2, 4, 6] := by
      rw [hPmWriter2]
      exact bw_softmax_shape_g199 _ _ [3, 2, 4] 6 (hx.shard_shapes _ (by simp))
    have hPmWriter3 : pmFinal 3003 = bw_softmax (pmFinal 1003) (pmFinal 2003) :=
      segment_000000_hPmWriter3 pmStore
    have hOutShape3 : (pmFinal 3003).shape = [3, 2, 4, 6] := by
      rw [hPmWriter3]
      exact bw_softmax_shape_g199 _ _ [3, 2, 4] 6 (hx.shard_shapes _ (by simp))
    have hcomm := TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim1_rank4 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 4 3 2 4 6
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp) (by simp) hg.shard_shapes hx.shard_shapes
    have hOutValue : smFinal 300 = allGatherPrimDimN 1 4 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] := by
      rw [hSmWriter, hgValue, hxValue, hcomm]
      simp only [List.zipWith]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2, ← hPmWriter3]
    have hOutValueList : smFinal 300 = allGatherPrimDimN 1 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003].length 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 300).shape = [3, 8, 4, 6] := by
      rw [hSmWriter]
      exact bw_softmax_shape_g199 _ _ [3, 8, 4] 6 hx.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 1 [3, 8, 4, 6] [3, 2, 4, 6]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := hx.gather_dim_lt
        shard_shapes := ?_
        shape_contract := by
          simp only [List.length_cons, List.length_nil]
          native_decide
      }
      intro piece hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2 | h3
      · subst piece
        exact hOutShape0
      · subst piece
        exact hOutShape1
      · subst piece
        exact hOutShape2
      · subst piece
        exact hOutShape3
    intro fact hfact
    have covered : fact ∈ [fo] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fo] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate BWSoftmaxA1Case2.smGraph BWSoftmaxA1Case2.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSoftmaxA1Case2
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSoftmaxA2Case0
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] }
def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }] }
def fg : RelationFact := .sharded 100 [1000, 1001] 2 [1, 4, 16, 8] [1, 4, 8, 8]
def fx : RelationFact := .sharded 200 [2000, 2001] 2 [1, 4, 16, 8] [1, 4, 8, 8]
def fo : RelationFact := .sharded 300 [3000, 3001] 2 [1, 4, 16, 8] [1, 4, 8, 8]
def state_000000 : RelationState where
  facts := [fg, fx]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fg, fx, fo]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.smGraph) smStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case0.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } 300
      (fun t => bw_softmax (t 100) (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case0.smGraph t 0 100 200 300 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case0.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case0.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
    calc
      _ = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.smGraph) smStore 200) := hout_prefix
      _ = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 2000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } 3000
      (fun t => bw_softmax (t 1000) (t 2000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case0.pmGraph t 0 1000 2000 3000 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 2000) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3001 = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 2001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } 3001
      (fun t => bw_softmax (t 1001) (t 2001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case0.pmGraph t 1 1001 2001 3001 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 2001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case0.pmGraph) pmStore 2001) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by rw [hout_read_0, hout_read_1]
  exact hout

set_option maxHeartbeats 500000 in
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
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001] 2 [1, 4, 16, 8] [1, 4, 8, 8] at hg
    have hx : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001] 2 [1, 4, 16, 8] [1, 4, 8, 8] at hx
    have hgValue : smFinal 100 = allGatherPrimDimN 2 2 0 [pmFinal 1000, pmFinal 1001] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hxValue : smFinal 200 = allGatherPrimDimN 2 2 0 [pmFinal 2000, pmFinal 2001] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 300 = bw_softmax (smFinal 100) (smFinal 200) :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 3000 = bw_softmax (pmFinal 1000) (pmFinal 2000) :=
      segment_000000_hPmWriter0 pmStore
    have hOutShape0 : (pmFinal 3000).shape = [1, 4, 8, 8] := by
      rw [hPmWriter0]
      exact bw_softmax_shape_g199 _ _ [1, 4, 8] 8 (hx.shard_shapes _ (by simp))
    have hPmWriter1 : pmFinal 3001 = bw_softmax (pmFinal 1001) (pmFinal 2001) :=
      segment_000000_hPmWriter1 pmStore
    have hOutShape1 : (pmFinal 3001).shape = [1, 4, 8, 8] := by
      rw [hPmWriter1]
      exact bw_softmax_shape_g199 _ _ [1, 4, 8] 8 (hx.shard_shapes _ (by simp))
    have hcomm := TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim2_rank4 [pmFinal 1000, pmFinal 1001] [pmFinal 2000, pmFinal 2001] 2 1 4 8 8
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp) (by simp) hg.shard_shapes hx.shard_shapes
    have hOutValue : smFinal 300 = allGatherPrimDimN 2 2 0 [pmFinal 3000, pmFinal 3001] := by
      rw [hSmWriter, hgValue, hxValue, hcomm]
      simp only [List.zipWith]
      rw [← hPmWriter0, ← hPmWriter1]
    have hOutValueList : smFinal 300 = allGatherPrimDimN 2 [pmFinal 3000, pmFinal 3001].length 0 [pmFinal 3000, pmFinal 3001] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 300).shape = [1, 4, 16, 8] := by
      rw [hSmWriter]
      exact bw_softmax_shape_g199 _ _ [1, 4, 16] 8 hx.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001] 2 [1, 4, 16, 8] [1, 4, 8, 8]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := hx.gather_dim_lt
        shard_shapes := ?_
        shape_contract := by
          simp only [List.length_cons, List.length_nil]
          native_decide
      }
      intro piece hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1
      · subst piece
        exact hOutShape0
      · subst piece
        exact hOutShape1
    intro fact hfact
    have covered : fact ∈ [fo] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fo] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate BWSoftmaxA2Case0.smGraph BWSoftmaxA2Case0.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSoftmaxA2Case0
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSoftmaxA2Case1
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }, { rank := 2, op := "OpName.FW_contiguous", ins := [8002], outs := [9002] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }] }
def fg : RelationFact := .sharded 100 [1000, 1001, 1002] 2 [2, 3, 15, 7] [2, 3, 5, 7]
def fx : RelationFact := .sharded 200 [2000, 2001, 2002] 2 [2, 3, 15, 7] [2, 3, 5, 7]
def fo : RelationFact := .sharded 300 [3000, 3001, 3002] 2 [2, 3, 15, 7] [2, 3, 5, 7]
def state_000000 : RelationState where
  facts := [fg, fx]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fg, fx, fo]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }, { rank := 2, op := "OpName.FW_contiguous", ins := [8002], outs := [9002] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.smGraph) smStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case1.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } 300
      (fun t => bw_softmax (t 100) (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case1.smGraph t 0 100 200 300 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case1.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case1.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
    calc
      _ = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.smGraph) smStore 200) := hout_prefix
      _ = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 2000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } 3000
      (fun t => bw_softmax (t 1000) (t 2000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case1.pmGraph t 0 1000 2000 3000 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 2000) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3001 = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 2001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } 3001
      (fun t => bw_softmax (t 1001) (t 2001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case1.pmGraph t 1 1001 2001 3001 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 2001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 2001) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3002 = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 2002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } 3002
      (fun t => bw_softmax (t 1002) (t 2002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case1.pmGraph t 2 1002 2002 3002 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 2002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case1.pmGraph) pmStore 2002) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by rw [hout_read_0, hout_read_1]
  exact hout

set_option maxHeartbeats 500000 in
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
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 2 [2, 3, 15, 7] [2, 3, 5, 7] at hg
    have hx : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 2 [2, 3, 15, 7] [2, 3, 5, 7] at hx
    have hgValue : smFinal 100 = allGatherPrimDimN 2 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hxValue : smFinal 200 = allGatherPrimDimN 2 3 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 300 = bw_softmax (smFinal 100) (smFinal 200) :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 3000 = bw_softmax (pmFinal 1000) (pmFinal 2000) :=
      segment_000000_hPmWriter0 pmStore
    have hOutShape0 : (pmFinal 3000).shape = [2, 3, 5, 7] := by
      rw [hPmWriter0]
      exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 (hx.shard_shapes _ (by simp))
    have hPmWriter1 : pmFinal 3001 = bw_softmax (pmFinal 1001) (pmFinal 2001) :=
      segment_000000_hPmWriter1 pmStore
    have hOutShape1 : (pmFinal 3001).shape = [2, 3, 5, 7] := by
      rw [hPmWriter1]
      exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 (hx.shard_shapes _ (by simp))
    have hPmWriter2 : pmFinal 3002 = bw_softmax (pmFinal 1002) (pmFinal 2002) :=
      segment_000000_hPmWriter2 pmStore
    have hOutShape2 : (pmFinal 3002).shape = [2, 3, 5, 7] := by
      rw [hPmWriter2]
      exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 (hx.shard_shapes _ (by simp))
    have hcomm := TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim2_rank4 [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] 3 2 3 5 7
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp) (by simp) hg.shard_shapes hx.shard_shapes
    have hOutValue : smFinal 300 = allGatherPrimDimN 2 3 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002] := by
      rw [hSmWriter, hgValue, hxValue, hcomm]
      simp only [List.zipWith]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
    have hOutValueList : smFinal 300 = allGatherPrimDimN 2 [pmFinal 3000, pmFinal 3001, pmFinal 3002].length 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 300).shape = [2, 3, 15, 7] := by
      rw [hSmWriter]
      exact bw_softmax_shape_g199 _ _ [2, 3, 15] 7 hx.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002] 2 [2, 3, 15, 7] [2, 3, 5, 7]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := hx.gather_dim_lt
        shard_shapes := ?_
        shape_contract := by
          simp only [List.length_cons, List.length_nil]
          native_decide
      }
      intro piece hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2
      · subst piece
        exact hOutShape0
      · subst piece
        exact hOutShape1
      · subst piece
        exact hOutShape2
    intro fact hfact
    have covered : fact ∈ [fo] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fo] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate BWSoftmaxA2Case1.smGraph BWSoftmaxA2Case1.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSoftmaxA2Case1
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSoftmaxA2Case2
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }, { rank := 2, op := "OpName.FW_contiguous", ins := [8002], outs := [9002] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }, { rank := 3, op := "OpName.FW_contiguous", ins := [8003], outs := [9003] }, { rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] }] }
def fg : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 2 [3, 2, 16, 6] [3, 2, 4, 6]
def fx : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 2 [3, 2, 16, 6] [3, 2, 4, 6]
def fo : RelationFact := .sharded 300 [3000, 3001, 3002, 3003] 2 [3, 2, 16, 6] [3, 2, 4, 6]
def state_000000 : RelationState where
  facts := [fg, fx]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fg, fx, fo]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [800], outs := [801] }, { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [8000], outs := [9000] }, { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }, { rank := 1, op := "OpName.FW_contiguous", ins := [8001], outs := [9001] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }, { rank := 2, op := "OpName.FW_contiguous", ins := [8002], outs := [9002] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }, { rank := 3, op := "OpName.FW_contiguous", ins := [8003], outs := [9003] }, { rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.smGraph) smStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case2.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } 300
      (fun t => bw_softmax (t 100) (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case2.smGraph t 0 100 200 300 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_sm_nodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
    calc
      _ = bw_softmax (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.smGraph) smStore 200) := hout_prefix
      _ = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } 3000
      (fun t => bw_softmax (t 1000) (t 2000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case2.pmGraph t 0 1000 2000 3000 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2000) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3001 = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } 3001
      (fun t => bw_softmax (t 1001) (t 2001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case2.pmGraph t 1 1001 2001 3001 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001], params := [3] } :: (segment_000000_pm_nodes.drop 4)) 2001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2001) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3002 = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } 3002
      (fun t => bw_softmax (t 1002) (t 2002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case2.pmGraph t 2 1002 2002 3002 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 2002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2002) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3003 = bw_softmax ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3003 = bw_softmax (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] } 3003
      (fun t => bw_softmax (t 1003) (t 2003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxA2Case2.pmGraph t 3 1003 2003 3003 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] } :: (segment_000000_pm_nodes.drop 8)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003], params := [3] } :: (segment_000000_pm_nodes.drop 8)) 2003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3003 = bw_softmax ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxA2Case2.pmGraph) pmStore 2003) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) := by rw [hout_read_0, hout_read_1]
  exact hout

set_option maxHeartbeats 500000 in
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
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 2 [3, 2, 16, 6] [3, 2, 4, 6] at hg
    have hx : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 2 [3, 2, 16, 6] [3, 2, 4, 6] at hx
    have hgValue : smFinal 100 = allGatherPrimDimN 2 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hxValue : smFinal 200 = allGatherPrimDimN 2 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 300 = bw_softmax (smFinal 100) (smFinal 200) :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 3000 = bw_softmax (pmFinal 1000) (pmFinal 2000) :=
      segment_000000_hPmWriter0 pmStore
    have hOutShape0 : (pmFinal 3000).shape = [3, 2, 4, 6] := by
      rw [hPmWriter0]
      exact bw_softmax_shape_g199 _ _ [3, 2, 4] 6 (hx.shard_shapes _ (by simp))
    have hPmWriter1 : pmFinal 3001 = bw_softmax (pmFinal 1001) (pmFinal 2001) :=
      segment_000000_hPmWriter1 pmStore
    have hOutShape1 : (pmFinal 3001).shape = [3, 2, 4, 6] := by
      rw [hPmWriter1]
      exact bw_softmax_shape_g199 _ _ [3, 2, 4] 6 (hx.shard_shapes _ (by simp))
    have hPmWriter2 : pmFinal 3002 = bw_softmax (pmFinal 1002) (pmFinal 2002) :=
      segment_000000_hPmWriter2 pmStore
    have hOutShape2 : (pmFinal 3002).shape = [3, 2, 4, 6] := by
      rw [hPmWriter2]
      exact bw_softmax_shape_g199 _ _ [3, 2, 4] 6 (hx.shard_shapes _ (by simp))
    have hPmWriter3 : pmFinal 3003 = bw_softmax (pmFinal 1003) (pmFinal 2003) :=
      segment_000000_hPmWriter3 pmStore
    have hOutShape3 : (pmFinal 3003).shape = [3, 2, 4, 6] := by
      rw [hPmWriter3]
      exact bw_softmax_shape_g199 _ _ [3, 2, 4] 6 (hx.shard_shapes _ (by simp))
    have hcomm := TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim2_rank4 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 4 3 2 4 6
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp) (by simp) hg.shard_shapes hx.shard_shapes
    have hOutValue : smFinal 300 = allGatherPrimDimN 2 4 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] := by
      rw [hSmWriter, hgValue, hxValue, hcomm]
      simp only [List.zipWith]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2, ← hPmWriter3]
    have hOutValueList : smFinal 300 = allGatherPrimDimN 2 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003].length 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 300).shape = [3, 2, 16, 6] := by
      rw [hSmWriter]
      exact bw_softmax_shape_g199 _ _ [3, 2, 16] 6 hx.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 2 [3, 2, 16, 6] [3, 2, 4, 6]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := hx.gather_dim_lt
        shard_shapes := ?_
        shape_contract := by
          simp only [List.length_cons, List.length_nil]
          native_decide
      }
      intro piece hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2 | h3
      · subst piece
        exact hOutShape0
      · subst piece
        exact hOutShape1
      · subst piece
        exact hOutShape2
      · subst piece
        exact hOutShape3
    intro fact hfact
    have covered : fact ∈ [fo] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fo] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate BWSoftmaxA2Case2.smGraph BWSoftmaxA2Case2.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSoftmaxA2Case2
