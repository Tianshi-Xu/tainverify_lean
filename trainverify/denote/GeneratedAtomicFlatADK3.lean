import denote.RelationCompiler
import denote.KRankViewFlatten
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace FlattenAllToAllDiv
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_div", ins := [700, 999], outs := [701], params := [4] }, { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 3] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 3] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 3] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] }, { rank := 0, op := "OpName.BW_div", ins := [8000, 9000], outs := [8100], params := [4] }, { rank := 1, op := "OpName.BW_div", ins := [8001, 9001], outs := [8101], params := [4] }, { rank := 2, op := "OpName.BW_div", ins := [8002, 9002], outs := [8102], params := [4] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 15, 3, 7] [2, 5, 3, 7]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002] 1 [2, 15, 21] [2, 5, 21]
def fact_ai : RelationFact := .sharded 700 [7000, 7001, 7002] 1 [2, 15, 3, 21] [2, 5, 3, 21]
def fact_ao : RelationFact := .sharded 700 [8000, 8001, 8002] 3 [2, 15, 3, 21] [2, 15, 3, 7]
def fact_do : RelationFact := .sharded 701 [8100, 8101, 8102] 3 [2, 15, 3, 21] [2, 15, 3, 7]
def state_000000 : RelationState where
  facts := [fact_x, fact_ai]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_out, fact_do]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_div", ins := [700, 999], outs := [701], params := [4] }, { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 3] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 3] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 3] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] }, { rank := 0, op := "OpName.BW_div", ins := [8000, 9000], outs := [8100], params := [4] }, { rank := 1, op := "OpName.BW_div", ins := [8001, 9001], outs := [8101], params := [4] }, { rank := 2, op := "OpName.BW_div", ins := [8002, 9002], outs := [8102], params := [4] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) s
private theorem segment_000000_hViewS (store : Store) : (segment_000000_sm_final store) 200 = fw_view [2, 15, 21] ((segment_000000_sm_final store) 100) := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 200 = fw_view [2, 15, 21] (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.smGraph) store 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.smGraph store
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] } 200
      (fun t => fw_view [2, 15, 21] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_view_out FlattenAllToAllDiv.smGraph t 0 2 [15, 21] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.smGraph store
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 200 = fw_view [2, 15, 21] ((segment_000000_sm_final store) 100) := by
    calc
      _ = fw_view [2, 15, 21] (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.smGraph) store 100) := hout_prefix
      _ = fw_view [2, 15, 21] ((segment_000000_sm_final store) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hViewP0 (store : Store) : (segment_000000_pm_final store) 2000 = fw_view [2, 5, 21] ((segment_000000_pm_final store) 1000) := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 2000 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] } 2000
      (fun t => fw_view [2, 5, 21] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_view_out FlattenAllToAllDiv.pmGraph t 0 2 [5, 21] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 2000 = fw_view [2, 5, 21] ((segment_000000_pm_final store) 1000) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 1000) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final store) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hViewP1 (store : Store) : (segment_000000_pm_final store) 2001 = fw_view [2, 5, 21] ((segment_000000_pm_final store) 1001) := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 2001 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] } 2001
      (fun t => fw_view [2, 5, 21] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_view_out FlattenAllToAllDiv.pmGraph t 1 2 [5, 21] 1001 8001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 2001 = fw_view [2, 5, 21] ((segment_000000_pm_final store) 1001) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 1001) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final store) 1001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hViewP2 (store : Store) : (segment_000000_pm_final store) 2002 = fw_view [2, 5, 21] ((segment_000000_pm_final store) 1002) := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 2002 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] } 2002
      (fun t => fw_view [2, 5, 21] (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_view_out FlattenAllToAllDiv.pmGraph t 2 2 [5, 21] 1002 8002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 1002 = (segment_000000_pm_final store) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 6)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 2002 = fw_view [2, 5, 21] ((segment_000000_pm_final store) 1002) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 1002) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final store) 1002) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hA0 (store : Store) : (segment_000000_pm_final store) 8000 = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 0 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 3 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 3] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 8000 = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 0 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7000, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7001, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7002] 1 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 3] } 8000
      (fun t => allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 0 [t 7000, t 7001, t 7002] 1 3) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out FlattenAllToAllDiv.pmGraph t 0 [7000, 7001, 7002] 8000 1 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7000 = (segment_000000_pm_final store) 7000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 3] } :: (segment_000000_pm_nodes.drop 3)) 7000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7001 = (segment_000000_pm_final store) 7001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 3] } :: (segment_000000_pm_nodes.drop 3)) 7001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7002 = (segment_000000_pm_final store) 7002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 3] } :: (segment_000000_pm_nodes.drop 3)) 7002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 8000 = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 0 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 3 := by
    calc
      _ = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 0 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7000, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7001, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7002] 1 3 := hout_prefix
      _ = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 0 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 3 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hA1 (store : Store) : (segment_000000_pm_final store) 8001 = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 1 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 3 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 3] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 8001 = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 1 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7000, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7001, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7002] 1 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 3] } 8001
      (fun t => allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 1 [t 7000, t 7001, t 7002] 1 3) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out FlattenAllToAllDiv.pmGraph t 1 [7000, 7001, 7002] 8001 1 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7000 = (segment_000000_pm_final store) 7000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 3] } :: (segment_000000_pm_nodes.drop 4)) 7000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7001 = (segment_000000_pm_final store) 7001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 3] } :: (segment_000000_pm_nodes.drop 4)) 7001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7002 = (segment_000000_pm_final store) 7002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 3] } :: (segment_000000_pm_nodes.drop 4)) 7002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 8001 = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 1 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 3 := by
    calc
      _ = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 1 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7000, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7001, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7002] 1 3 := hout_prefix
      _ = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 1 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 3 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hA2 (store : Store) : (segment_000000_pm_final store) 8002 = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 2 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 3 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 3] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 8002 = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 2 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7000, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7001, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7002] 1 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 3] } 8002
      (fun t => allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 2 [t 7000, t 7001, t 7002] 1 3) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out FlattenAllToAllDiv.pmGraph t 2 [7000, 7001, 7002] 8002 1 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7000 = (segment_000000_pm_final store) 7000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 3] } :: (segment_000000_pm_nodes.drop 5)) 7000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7001 = (segment_000000_pm_final store) 7001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 3] } :: (segment_000000_pm_nodes.drop 5)) 7001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7002 = (segment_000000_pm_final store) 7002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 3] } :: (segment_000000_pm_nodes.drop 5)) 7002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 8002 = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 2 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 3 := by
    calc
      _ = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 2 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7000, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7001, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 7002] 1 3 := hout_prefix
      _ = allToAllPrimWithDims FlattenAllToAllDiv.pmGraph.numRanks 2 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 3 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hDivS (store : Store) : (segment_000000_sm_final store) 701 = bw_div (4 : Scalar) ((segment_000000_sm_final store) 700) := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_div", ins := [700, 999], outs := [701], params := [4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 701 = bw_div (4 : Scalar) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.smGraph) store 700) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_div", ins := [700, 999], outs := [701], params := [4] } 701
      (fun t => bw_div (4 : Scalar) (t 700)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_div_out_g128 FlattenAllToAllDiv.smGraph t 0 4 700 999 701
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.smGraph) store 700 = (segment_000000_sm_final store) 700 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_div", ins := [700, 999], outs := [701], params := [4] } :: (segment_000000_sm_nodes.drop 1)) 700
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 701 = bw_div (4 : Scalar) ((segment_000000_sm_final store) 700) := by
    calc
      _ = bw_div (4 : Scalar) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.smGraph) store 700) := hout_prefix
      _ = bw_div (4 : Scalar) ((segment_000000_sm_final store) 700) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hDivP0 (store : Store) : (segment_000000_pm_final store) 8100 = bw_div (4 : Scalar) ((segment_000000_pm_final store) 8000) := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 6) ++ [{ rank := 0, op := "OpName.BW_div", ins := [8000, 9000], outs := [8100], params := [4] }] ++ (segment_000000_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 8100 = bw_div (4 : Scalar) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 8000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 6) (segment_000000_pm_nodes.drop 7)
      { rank := 0, op := "OpName.BW_div", ins := [8000, 9000], outs := [8100], params := [4] } 8100
      (fun t => bw_div (4 : Scalar) (t 8000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_div_out_g128 FlattenAllToAllDiv.pmGraph t 0 4 8000 9000 8100
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 8000 = (segment_000000_pm_final store) 8000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_div", ins := [8000, 9000], outs := [8100], params := [4] } :: (segment_000000_pm_nodes.drop 7)) 8000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 8100 = bw_div (4 : Scalar) ((segment_000000_pm_final store) 8000) := by
    calc
      _ = bw_div (4 : Scalar) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 8000) := hout_prefix
      _ = bw_div (4 : Scalar) ((segment_000000_pm_final store) 8000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hDivP1 (store : Store) : (segment_000000_pm_final store) 8101 = bw_div (4 : Scalar) ((segment_000000_pm_final store) 8001) := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 1, op := "OpName.BW_div", ins := [8001, 9001], outs := [8101], params := [4] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 8101 = bw_div (4 : Scalar) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 8001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 1, op := "OpName.BW_div", ins := [8001, 9001], outs := [8101], params := [4] } 8101
      (fun t => bw_div (4 : Scalar) (t 8001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_div_out_g128 FlattenAllToAllDiv.pmGraph t 1 4 8001 9001 8101
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 8001 = (segment_000000_pm_final store) 8001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_div", ins := [8001, 9001], outs := [8101], params := [4] } :: (segment_000000_pm_nodes.drop 8)) 8001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 8101 = bw_div (4 : Scalar) ((segment_000000_pm_final store) 8001) := by
    calc
      _ = bw_div (4 : Scalar) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 8001) := hout_prefix
      _ = bw_div (4 : Scalar) ((segment_000000_pm_final store) 8001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hDivP2 (store : Store) : (segment_000000_pm_final store) 8102 = bw_div (4 : Scalar) ((segment_000000_pm_final store) 8002) := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 8) ++ [{ rank := 2, op := "OpName.BW_div", ins := [8002, 9002], outs := [8102], params := [4] }] ++ (segment_000000_pm_nodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 8102 = bw_div (4 : Scalar) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 8002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 8) (segment_000000_pm_nodes.drop 9)
      { rank := 2, op := "OpName.BW_div", ins := [8002, 9002], outs := [8102], params := [4] } 8102
      (fun t => bw_div (4 : Scalar) (t 8002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_div_out_g128 FlattenAllToAllDiv.pmGraph t 2 4 8002 9002 8102
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 8002 = (segment_000000_pm_final store) 8002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FlattenAllToAllDiv.pmGraph store
      (segment_000000_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_div", ins := [8002, 9002], outs := [8102], params := [4] } :: (segment_000000_pm_nodes.drop 9)) 8002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 8102 = bw_div (4 : Scalar) ((segment_000000_pm_final store) 8002) := by
    calc
      _ = bw_div (4 : Scalar) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful FlattenAllToAllDiv.pmGraph) store 8002) := hout_prefix
      _ = bw_div (4 : Scalar) ((segment_000000_pm_final store) 8002) := by rw [hout_read_0]
  exact hout
set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_000000.Holds smStore pmStore) : state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
 let smFinal := segment_000000_sm_final smStore
 let pmFinal := segment_000000_pm_final pmStore
 have hframe : state_000000.Holds smFinal pmFinal := by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final; apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
 have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 1 [2, 15, 3, 7] [2, 5, 3, 7] at hx
 have hVS : smFinal 200 = fw_view [2, 15, 21] (smFinal 100) := segment_000000_hViewS smStore
 have hxV : smFinal 100 = allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002] := hx.full_value
 have hVP0 : pmFinal 2000 = fw_view [2, 5, 21] (pmFinal 1000) := segment_000000_hViewP0 pmStore
 have hVP1 : pmFinal 2001 = fw_view [2, 5, 21] (pmFinal 1001) := segment_000000_hViewP1 pmStore
 have hVP2 : pmFinal 2002 = fw_view [2, 5, 21] (pmFinal 1002) := segment_000000_hViewP2 pmStore
 have hVC := TrainVerify.Denote.fw_view_allGatherPrimDimN_dim1_rank4_to_rank3 3 2 5 3 7 [pmFinal 1000, pmFinal 1001, pmFinal 1002] (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
 have hVV : smFinal 200 = allGatherPrimDimN 1 3 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002] := by rw [hVS,hxV,hVC]; simp only [List.map]; rw [← hVP0, ← hVP1, ← hVP2]
 have hVF : (smFinal 200).shape = [2, 15, 21] := by rw [hVS]; rfl
 have hVShape0 : (pmFinal 2000).shape = [2, 5, 21] := by rw [hVP0]; rfl
 have hVShape1 : (pmFinal 2001).shape = [2, 5, 21] := by rw [hVP1]; rfl
 have hVShape2 : (pmFinal 2002).shape = [2, 5, 21] := by rw [hVP2]; rfl
 have houtV : fact_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 1 [2, 15, 21] [2, 5, 21]
   refine { full_value := hVV, full_shape := hVF, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simp only [List.forall_mem_cons]; exact ⟨hVShape0, hVShape1, hVShape2, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 have hai : fact_ai.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 700) [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 [2, 15, 3, 21] [2, 5, 3, 21] at hai
 have hA0 : pmFinal 8000 = allToAllPrimWithDims 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 3 := segment_000000_hA0 pmStore
 have hA1 : pmFinal 8001 = allToAllPrimWithDims 3 1 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 3 := segment_000000_hA1 pmStore
 have hA2 : pmFinal 8002 = allToAllPrimWithDims 3 2 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 3 := segment_000000_hA2 pmStore
 have hHead : (([pmFinal 7000, pmFinal 7001, pmFinal 7002].head?.map (fun t => t.shape)).getD []) = [2, 5, 3, 21] := hai.shard_shapes _ (by simp)
 have hAV : smFinal 700 = allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002] := hai.full_value
 have hGS : (allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002]).shape = [2, 15, 3, 21] := by rw [← hAV]; exact hai.full_shape
 have hOd : 3 < (allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002]).shape.length := by rw [hGS]; decide
 have hDv : (allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002]).shape.getD 3 0 % 3 = 0 := by rw [hGS]; decide
 have hAS0 : (pmFinal 8000).shape = [2, 15, 3, 7] := by rw [hA0,allToAllPrimWithDims_shape 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 3 [2, 5, 3, 21] hHead (by decide)]; decide
 have hAS1 : (pmFinal 8001).shape = [2, 15, 3, 7] := by rw [hA1,allToAllPrimWithDims_shape 3 1 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 3 [2, 5, 3, 21] hHead (by decide)]; decide
 have hAS2 : (pmFinal 8002).shape = [2, 15, 3, 7] := by rw [hA2,allToAllPrimWithDims_shape 3 2 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 3 [2, 5, 3, 21] hHead (by decide)]; decide
 have hOrd : [pmFinal 8000, pmFinal 8001, pmFinal 8002] = List.ofFn (fun r : Fin 3 => allToAllPrimWithDims 3 r.1 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 3) := by rw [hA0, hA1, hA2]; rfl
 have hAC : allGatherPrimDimN 3 [pmFinal 8000, pmFinal 8001, pmFinal 8002].length 0 [pmFinal 8000, pmFinal 8001, pmFinal 8002] = allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002] := by rw [hOrd]; simpa only [List.length_cons,List.length_nil,List.length_ofFn] using (TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 3 [pmFinal 7000, pmFinal 7001, pmFinal 7002] (by simp) hOd hDv)
 have hAO : smFinal 700 = allGatherPrimDimN 3 [pmFinal 8000, pmFinal 8001, pmFinal 8002].length 0 [pmFinal 8000, pmFinal 8001, pmFinal 8002] := by rw [hAC]; exact hAV
 have houtA : fact_ao.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 700) [pmFinal 8000, pmFinal 8001, pmFinal 8002] 3 [2, 15, 3, 21] [2, 15, 3, 7]
   refine { full_value := hAO, full_shape := hai.full_shape, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simp only [List.forall_mem_cons]; exact ⟨hAS0, hAS1, hAS2, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 have hdi := houtA
 change ShardedRel (smFinal 700) [pmFinal 8000, pmFinal 8001, pmFinal 8002] 3 [2, 15, 3, 21] [2, 15, 3, 7] at hdi
 have hDS : smFinal 701 = bw_div (4 : Scalar) (smFinal 700) := segment_000000_hDivS smStore
 have hDP0 : pmFinal 8100 = bw_div (4 : Scalar) (pmFinal 8000) := segment_000000_hDivP0 pmStore
 have hDShape0 : (pmFinal 8100).shape = [2, 15, 3, 7] := by rw [hDP0,bw_div_shape_g128]; exact hdi.shard_shapes _ (by simp)
 have hDP1 : pmFinal 8101 = bw_div (4 : Scalar) (pmFinal 8001) := segment_000000_hDivP1 pmStore
 have hDShape1 : (pmFinal 8101).shape = [2, 15, 3, 7] := by rw [hDP1,bw_div_shape_g128]; exact hdi.shard_shapes _ (by simp)
 have hDP2 : pmFinal 8102 = bw_div (4 : Scalar) (pmFinal 8002) := segment_000000_hDivP2 pmStore
 have hDShape2 : (pmFinal 8102).shape = [2, 15, 3, 7] := by rw [hDP2,bw_div_shape_g128]; exact hdi.shard_shapes _ (by simp)
 have hDC := TrainVerify.Denote.bw_div_allGatherPrimDimN_eq_g128 (4 : Scalar) 3 3 [pmFinal 8000, pmFinal 8001, pmFinal 8002] [2, 15, 3, 7] (by decide) rfl (hdi.shard_shapes _ (by simp)) (by intro i hi; exact hdi.shard_shapes _ (List.get_mem _ _))
 have hDV : smFinal 701 = allGatherPrimDimN 3 3 0 [pmFinal 8100, pmFinal 8101, pmFinal 8102] := by rw [hDS,hdi.full_value]; simp only [List.length_cons,List.length_nil]; rw [hDC]; simp only [List.map]; rw [← hDP0, ← hDP1, ← hDP2]
 have hDF : (smFinal 701).shape = [2, 15, 3, 21] := by rw [hDS,bw_div_shape_g128]; exact hdi.full_shape
 have houtD : fact_do.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 701) [pmFinal 8100, pmFinal 8101, pmFinal 8102] 3 [2, 15, 3, 21] [2, 15, 3, 7]
   refine { full_value := hDV, full_shape := hDF, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simp only [List.forall_mem_cons]; exact ⟨hDShape0, hDShape1, hDShape2, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 intro fact hfact
 have hc : fact ∈ [fact_out, fact_ao, fact_do] ++ state_000000.facts := (show state_000001.facts ⊆ [fact_out, fact_ao, fact_do] ++ state_000000.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh | old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
   rcases fresh with rfl | rfl | rfl
   · exact houtV
   · exact houtA
   · exact houtD
 · exact hframe fact old
private def segment_000000 : ClosedDepSegmentCertificate FlattenAllToAllDiv.smGraph FlattenAllToAllDiv.pmGraph state_000000 state_000001 where
 smNodes := segment_000000_sm_nodes
 pmNodes := segment_000000_pm_nodes
 sound := by intro x y h; have z := segment_000000_sound x y h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000
end
end FlattenAllToAllDiv
