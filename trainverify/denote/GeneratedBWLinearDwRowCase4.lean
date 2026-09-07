import denote.RelationCompiler
import denote.KRankBWLinearDwRowGeneral
import denote.KRankBWLinearDxRow
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLinearDwRow
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }, { rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [10, 11] }] }
def pmGraph : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_linear", ins := [1004, 2000, 3004], outs := [4004, 5004] }, { rank := 0, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [10, 11] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003, 1004] 2 [2, 5, 35] [2, 5, 7]
def fact_x : RelationFact := .joined 200 2000 [2, 5, 11]
def fact_w : RelationFact := .sharded 300 [3000, 3001, 3002, 3003, 3004] 0 [35, 11] [7, 11]
def fact_dw : RelationFact := .sharded 401 [5000, 5001, 5002, 5003, 5004] 0 [35, 11] [7, 11]
def fact_tail_in : RelationFact := .joined 600 6000 [2, 5, 11]
def fact_tail_out : RelationFact := .joined 700 7000 [10, 11]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_tail_in]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_tail_in, fact_dw, fact_tail_out]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }, { rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [10, 11] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_linear", ins := [1004, 2000, 3004], outs := [4004, 5004] }, { rank := 0, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [10, 11] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) store

private theorem segment_000000_hSmDwWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 401 =
      (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDwRow.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_linear (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticBWLinearDwRow.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmDwWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5000 =
      (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_linear (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticBWLinearDwRow.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmDwWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5001 =
      (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3001)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } 5001
      (fun t => (bw_linear (t 1001) (t 2000) (t 3001)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticBWLinearDwRow.pmGraph t 1 1001 2000 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3001)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmDwWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5002 =
      (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3002)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } 5002
      (fun t => (bw_linear (t 1002) (t 2000) (t 3002)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticBWLinearDwRow.pmGraph t 2 1002 2000 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3002)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmDwWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5003 =
      (bw_linear ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3003)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5003 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3003)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } 5003
      (fun t => (bw_linear (t 1003) (t 2000) (t 3003)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticBWLinearDwRow.pmGraph t 3 1003 2000 3003 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3003 = (segment_000000_pm_final pmStore) 3003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5003 = (bw_linear ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3003)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3003)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3003)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmDwWriter4 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5004 =
      (bw_linear ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3004)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 4, op := "OpName.BW_linear", ins := [1004, 2000, 3004], outs := [4004, 5004] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5004 = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3004)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 4, op := "OpName.BW_linear", ins := [1004, 2000, 3004], outs := [4004, 5004] } 5004
      (fun t => (bw_linear (t 1004) (t 2000) (t 3004)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticBWLinearDwRow.pmGraph t 4 1004 2000 3004 4004 5004 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1004 = (segment_000000_pm_final pmStore) 1004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_linear", ins := [1004, 2000, 3004], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 1004
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_linear", ins := [1004, 2000, 3004], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3004 = (segment_000000_pm_final pmStore) 3004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_linear", ins := [1004, 2000, 3004], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 3004
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5004 = (bw_linear ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3004)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 3004)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3004)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hViewSm (smStore:Store) : (segment_000000_sm_final smStore) 700 = fw_view [10, 11] ((segment_000000_sm_final smStore) 600) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [10, 11] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 700 = fw_view [10, 11] (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 600) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDwRow.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [10, 11] } 700
      (fun t => fw_view [10, 11] (t 600)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_view_out SyntheticBWLinearDwRow.smGraph t 0 10 [11] 600 601 700
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 600 = (segment_000000_sm_final smStore) 600 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [10, 11] } :: (segment_000000_sm_nodes.drop 2)) 600
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 700 = fw_view [10, 11] ((segment_000000_sm_final smStore) 600) := by
    calc
      _ = fw_view [10, 11] (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.smGraph) smStore 600) := hout_prefix
      _ = fw_view [10, 11] ((segment_000000_sm_final smStore) 600) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hViewPm (pmStore:Store) : (segment_000000_pm_final pmStore) 7000 = fw_view [10, 11] ((segment_000000_pm_final pmStore) 6000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 0, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [10, 11] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7000 = fw_view [10, 11] (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 6000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 0, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [10, 11] } 7000
      (fun t => fw_view [10, 11] (t 6000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_view_out SyntheticBWLinearDwRow.pmGraph t 0 10 [11] 6000 6001 7000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 6000 = (segment_000000_pm_final pmStore) 6000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDwRow.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 0, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [10, 11] } :: (segment_000000_pm_nodes.drop 6)) 6000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7000 = fw_view [10, 11] ((segment_000000_pm_final pmStore) 6000) := by
    calc
      _ = fw_view [10, 11] (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDwRow.pmGraph) pmStore 6000) := hout_prefix
      _ = fw_view [10, 11] ((segment_000000_pm_final pmStore) 6000) := by rw [hout_read_0]
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
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] 2 [2, 5, 35] [2, 5, 7] at hg
    have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
    change smFinal 200 = pmFinal 2000 ∧
      (smFinal 200).shape = [2, 5, 11] ∧
      (pmFinal 2000).shape = [2, 5, 11] at hx
    have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004] 0 [35, 11] [7, 11] at hw
    have hgValue : smFinal 100 = allGatherPrimDimN 2 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hwValue : smFinal 300 = allGatherPrimDimN 0 5 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004] := by
      simpa only [List.length_cons, List.length_nil] using hw.full_value
    have hSmDwWriter : smFinal 401 =
        (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).2 :=
      segment_000000_hSmDwWriter smStore
    have hvi : fact_tail_in.Holds smFinal pmFinal := hframe _ (by native_decide)
    have hvs := segment_000000_hViewSm smStore
    have hvp := segment_000000_hViewPm pmStore
    change smFinal 700 = fw_view [10, 11] (smFinal 600) at hvs
    change pmFinal 7000 = fw_view [10, 11] (pmFinal 6000) at hvp
    have houtView : fact_tail_out.Holds smFinal pmFinal := by
      change smFinal 700 = pmFinal 7000 ∧ _ ∧ _
      rw [hvs, hvp]
      exact JoinedRel.fw_view [10, 11] [2, 5, 11] hvi
    have hPmDwWriter0 : pmFinal 5000 =
        (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2 :=
      segment_000000_hPmDwWriter0 pmStore
    have hgShape0 := hg.shard_shapes (pmFinal 1000) (by simp)
    have hwShape0 := hw.shard_shapes (pmFinal 3000) (by simp)
    have hDwOutShape0 : (pmFinal 5000).shape = [7, 11] := by
      rw [hPmDwWriter0]
      exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _
        hgShape0 hx.2.2 hwShape0
    have hPmDwWriter1 : pmFinal 5001 =
        (bw_linear (pmFinal 1001) (pmFinal 2000) (pmFinal 3001)).2 :=
      segment_000000_hPmDwWriter1 pmStore
    have hgShape1 := hg.shard_shapes (pmFinal 1001) (by simp)
    have hwShape1 := hw.shard_shapes (pmFinal 3001) (by simp)
    have hDwOutShape1 : (pmFinal 5001).shape = [7, 11] := by
      rw [hPmDwWriter1]
      exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _
        hgShape1 hx.2.2 hwShape1
    have hPmDwWriter2 : pmFinal 5002 =
        (bw_linear (pmFinal 1002) (pmFinal 2000) (pmFinal 3002)).2 :=
      segment_000000_hPmDwWriter2 pmStore
    have hgShape2 := hg.shard_shapes (pmFinal 1002) (by simp)
    have hwShape2 := hw.shard_shapes (pmFinal 3002) (by simp)
    have hDwOutShape2 : (pmFinal 5002).shape = [7, 11] := by
      rw [hPmDwWriter2]
      exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _
        hgShape2 hx.2.2 hwShape2
    have hPmDwWriter3 : pmFinal 5003 =
        (bw_linear (pmFinal 1003) (pmFinal 2000) (pmFinal 3003)).2 :=
      segment_000000_hPmDwWriter3 pmStore
    have hgShape3 := hg.shard_shapes (pmFinal 1003) (by simp)
    have hwShape3 := hw.shard_shapes (pmFinal 3003) (by simp)
    have hDwOutShape3 : (pmFinal 5003).shape = [7, 11] := by
      rw [hPmDwWriter3]
      exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _
        hgShape3 hx.2.2 hwShape3
    have hPmDwWriter4 : pmFinal 5004 =
        (bw_linear (pmFinal 1004) (pmFinal 2000) (pmFinal 3004)).2 :=
      segment_000000_hPmDwWriter4 pmStore
    have hgShape4 := hg.shard_shapes (pmFinal 1004) (by simp)
    have hwShape4 := hw.shard_shapes (pmFinal 3004) (by simp)
    have hDwOutShape4 : (pmFinal 5004).shape = [7, 11] := by
      rw [hPmDwWriter4]
      exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _
        hgShape4 hx.2.2 hwShape4
    have hDwCommRaw := TrainVerify.Denote.bw_linear_dw_row_allGather_rank3 5 2 5 7 11
      [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004] (pmFinal 2000)
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
      hg.shard_shapes hw.shard_shapes hx.2.2
    have hDwComm : (bw_linear (allGatherPrimDimN 2 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004])
        (pmFinal 2000) (allGatherPrimDimN 0 5 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004])).2 =
        allGatherPrimDimN 0 5 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2, (bw_linear (pmFinal 1001) (pmFinal 2000) (pmFinal 3001)).2, (bw_linear (pmFinal 1002) (pmFinal 2000) (pmFinal 3002)).2, (bw_linear (pmFinal 1003) (pmFinal 2000) (pmFinal 3003)).2, (bw_linear (pmFinal 1004) (pmFinal 2000) (pmFinal 3004)).2] := by
      simpa only [List.zipWith] using hDwCommRaw
    have hDwValue : smFinal 401 = allGatherPrimDimN 0 5 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003, pmFinal 5004] := by
      rw [hSmDwWriter, hgValue, hx.1, hwValue, hDwComm]
      rw [← hPmDwWriter0, ← hPmDwWriter1, ← hPmDwWriter2, ← hPmDwWriter3, ← hPmDwWriter4]
    have hDwValueList : smFinal 401 = allGatherPrimDimN 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003, pmFinal 5004].length 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003, pmFinal 5004] := by
      simpa only [List.length_cons, List.length_nil] using hDwValue
    have hDwFullShape : (smFinal 401).shape = [35, 11] := by
      rw [hSmDwWriter]
      exact bw_linear_3d_snd_shape 2 5 35 11 _ _ _
        hg.full_shape hx.2.1 hw.full_shape
    have houtDw : fact_dw.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 401) [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003, pmFinal 5004] 0 [35, 11] [7, 11]
      refine {
        full_value := hDwValueList
        full_shape := hDwFullShape
        shards_nonempty := by simp
        gather_dim_lt := by native_decide
        shard_shapes := ?_
        shape_contract := by simp
      }
      intro shard hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2 | h3 | h4
      · subst shard
        exact hDwOutShape0
      · subst shard
        exact hDwOutShape1
      · subst shard
        exact hDwOutShape2
      · subst shard
        exact hDwOutShape3
      · subst shard
        exact hDwOutShape4
    intro fact hfact
    have covered : fact ∈ [fact_dw, fact_tail_out] ++ state_before.facts := by
      exact (show state_after.facts ⊆ [fact_dw, fact_tail_out] ++ state_before.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · exact houtDw
      · exact houtView
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticBWLinearDwRow.smGraph SyntheticBWLinearDwRow.pmGraph state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end SyntheticBWLinearDwRow
