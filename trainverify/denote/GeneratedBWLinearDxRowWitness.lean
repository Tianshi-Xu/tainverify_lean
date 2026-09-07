import denote.RelationCompiler
import denote.KRankBWLinearDxRow
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLinearRow
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002] 2 [2, 5, 21] [2, 5, 7]
def fact_x : RelationFact := .joined 200 2000 [2, 5, 11]
def fact_w : RelationFact := .sharded 300 [3000, 3001, 3002] 0 [21, 11] [7, 11]
def fact_out : RelationFact := .reduction 400 [4000, 4001, 4002] [2, 5, 11]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_out]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 400 =
      (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearRow.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearRow.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 4000 =
      (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearRow.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 4001 =
      (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 3001)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1001) (t 2000) (t 3001)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearRow.pmGraph t 1 1001 2000 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 3001)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 4002 =
      (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 3002)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } 4002
      (fun t => (bw_linear (t 1002) (t 2000) (t 3002)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearRow.pmGraph t 2 1002 2000 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearRow.pmGraph) pmStore 3002)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
    let smFinal := segment_000000_sm_final smStore
    let pmFinal := segment_000000_pm_final pmStore
    have hframe : state_before.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 2 [2, 5, 21] [2, 5, 7] at hg
    have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
    change smFinal 200 = pmFinal 2000 ∧
      (smFinal 200).shape = [2, 5, 11] ∧
      (pmFinal 2000).shape = [2, 5, 11] at hx
    have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002] 0 [21, 11] [7, 11] at hw
    have hgValue : smFinal 100 = allGatherPrimDimN 2 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hwValue : smFinal 300 = allGatherPrimDimN 0 3 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002] := by
      simpa only [List.length_cons, List.length_nil] using hw.full_value
    have hSmWriter : smFinal 400 =
        (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).1 :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 4000 =
        (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1 :=
      segment_000000_hPmWriter0 pmStore
    have hgShape0 := hg.shard_shapes (pmFinal 1000) (by simp)
    have hwShape0 := hw.shard_shapes (pmFinal 3000) (by simp)
    have hOutShape0 : (pmFinal 4000).shape = [2, 5, 11] := by
      rw [hPmWriter0]
      exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _
        hgShape0 hx.2.2 hwShape0
    have hPmWriter1 : pmFinal 4001 =
        (bw_linear (pmFinal 1001) (pmFinal 2000) (pmFinal 3001)).1 :=
      segment_000000_hPmWriter1 pmStore
    have hgShape1 := hg.shard_shapes (pmFinal 1001) (by simp)
    have hwShape1 := hw.shard_shapes (pmFinal 3001) (by simp)
    have hOutShape1 : (pmFinal 4001).shape = [2, 5, 11] := by
      rw [hPmWriter1]
      exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _
        hgShape1 hx.2.2 hwShape1
    have hPmWriter2 : pmFinal 4002 =
        (bw_linear (pmFinal 1002) (pmFinal 2000) (pmFinal 3002)).1 :=
      segment_000000_hPmWriter2 pmStore
    have hgShape2 := hg.shard_shapes (pmFinal 1002) (by simp)
    have hwShape2 := hw.shard_shapes (pmFinal 3002) (by simp)
    have hOutShape2 : (pmFinal 4002).shape = [2, 5, 11] := by
      rw [hPmWriter2]
      exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _
        hgShape2 hx.2.2 hwShape2
    have hcomm_raw := TrainVerify.Denote.bw_linear_dx_row_reduction_rank3 3 2 5 7 11
      [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 3000, pmFinal 3001, pmFinal 3002] (pmFinal 2000)
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
      hg.shard_shapes hw.shard_shapes hx.2.2
    have hcomm : (bw_linear (allGatherPrimDimN 2 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002])
      (pmFinal 2000) (allGatherPrimDimN 0 3 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002])).1 =
      allReducePrim 3 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1, (bw_linear (pmFinal 1001) (pmFinal 2000) (pmFinal 3001)).1, (bw_linear (pmFinal 1002) (pmFinal 2000) (pmFinal 3002)).1] := by
      simpa only [List.zipWith, tensorSum, allReducePrim, List.head?_cons, Option.map_some, Option.getD_some] using hcomm_raw
    have hOutValue : smFinal 400 = allReducePrim 3 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002] := by
      rw [hSmWriter, hgValue, hx.1, hwValue, hcomm]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
    have hOutValueList : smFinal 400 =
        allReducePrim [pmFinal 4000, pmFinal 4001, pmFinal 4002].length 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 400).shape = [2, 5, 11] := by
      rw [hSmWriter]
      exact bw_linear_3d_fst_shape 2 5 21 11 _ _ _
        hg.full_shape hx.2.1 hw.full_shape
    have hout : fact_out.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002] [2, 5, 11]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        contributions_nonempty := by simp
        contribution_shapes := ?_
        reduced_shape := ?_
      }
      · intro contribution hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst contribution
          exact hOutShape0
        · subst contribution
          exact hOutShape1
        · subst contribution
          exact hOutShape2
      · rw [← hOutValueList]
        exact hFullShape
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_before.facts := by
      exact (show state_after.facts ⊆ [fact_out] ++ state_before.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticBWLinearRow.smGraph SyntheticBWLinearRow.pmGraph state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end SyntheticBWLinearRow
