import denote.RelationCompiler
import denote.KRankTranspose
import denote.KRankTranspose23Extra
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace TransposeAllToAll
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_transpose", ins := [200, 900], outs := [400], params := [2, 3] }, { rank := 0, op := "OpName.BW_transpose", ins := [100, 901], outs := [300], params := [1, 2] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_transpose", ins := [1000, 910], outs := [3000], params := [1, 2] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4000], params := [1, 2] }, { rank := 1, op := "OpName.BW_transpose", ins := [1001, 911], outs := [3001], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4001], params := [1, 2] }, { rank := 2, op := "OpName.BW_transpose", ins := [1002, 912], outs := [3002], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4002], params := [1, 2] }, { rank := 3, op := "OpName.BW_transpose", ins := [1003, 913], outs := [3003], params := [1, 2] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4003], params := [1, 2] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6000], params := [2, 1] }, { rank := 0, op := "OpName.BW_transpose", ins := [4000, 920], outs := [7000], params := [2, 3] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6001], params := [2, 1] }, { rank := 1, op := "OpName.BW_transpose", ins := [4001, 921], outs := [7001], params := [2, 3] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6002], params := [2, 1] }, { rank := 2, op := "OpName.BW_transpose", ins := [4002, 922], outs := [7002], params := [2, 3] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6003], params := [2, 1] }, { rank := 3, op := "OpName.BW_transpose", ins := [4003, 923], outs := [7003], params := [2, 3] }] }
def anchor : RelationFact := .tensorShape .sm 999 [1]
def input_t : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 1 [2, 12, 20, 7] [2, 3, 20, 7]
def input_a : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 1 [2, 12, 20, 7] [2, 3, 20, 7]
def input_b : RelationFact := .sharded 500 [5000, 5001, 5002, 5003] 2 [2, 12, 20, 7] [2, 12, 5, 7]
def out_t : RelationFact := .sharded 300 [3000, 3001, 3002, 3003] 2 [2, 20, 12, 7] [2, 20, 3, 7]
def out_a : RelationFact := .sharded 200 [4000, 4001, 4002, 4003] 2 [2, 12, 20, 7] [2, 12, 5, 7]
def out_c : RelationFact := .sharded 400 [7000, 7001, 7002, 7003] 3 [2, 12, 7, 20] [2, 12, 7, 5]
def out_b : RelationFact := .sharded 500 [6000, 6001, 6002, 6003] 1 [2, 12, 20, 7] [2, 3, 20, 7]
def before : RelationState where
  facts := [anchor, input_t, input_a, input_b]
  nonempty := by decide
def after : RelationState where
  facts := [anchor, input_t, input_a, input_b, out_t, out_c, out_b]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_transpose", ins := [200, 900], outs := [400], params := [2, 3] }, { rank := 0, op := "OpName.BW_transpose", ins := [100, 901], outs := [300], params := [1, 2] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_transpose", ins := [1000, 910], outs := [3000], params := [1, 2] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4000], params := [1, 2] }, { rank := 1, op := "OpName.BW_transpose", ins := [1001, 911], outs := [3001], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4001], params := [1, 2] }, { rank := 2, op := "OpName.BW_transpose", ins := [1002, 912], outs := [3002], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4002], params := [1, 2] }, { rank := 3, op := "OpName.BW_transpose", ins := [1003, 913], outs := [3003], params := [1, 2] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4003], params := [1, 2] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6000], params := [2, 1] }, { rank := 0, op := "OpName.BW_transpose", ins := [4000, 920], outs := [7000], params := [2, 3] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6001], params := [2, 1] }, { rank := 1, op := "OpName.BW_transpose", ins := [4001, 921], outs := [7001], params := [2, 3] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6002], params := [2, 1] }, { rank := 2, op := "OpName.BW_transpose", ins := [4002, 922], outs := [7002], params := [2, 3] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6003], params := [2, 1] }, { rank := 3, op := "OpName.BW_transpose", ins := [4003, 923], outs := [7003], params := [2, 3] }]
@[irreducible] private def segment_000000_sm_final (z : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.smGraph) z
@[irreducible] private def segment_000000_pm_final (z : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) z

private theorem segment_000000_hSm0 (smStore : Store) : (segment_000000_sm_final smStore) 300 = transposeAxes 1 2 ((segment_000000_sm_final smStore) 100) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [100, 901], outs := [300], params := [1, 2] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = transposeAxes 1 2 (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_transpose", ins := [100, 901], outs := [300], params := [1, 2] } 300
      (fun t => transposeAxes 1 2 (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.smGraph t 0 100 901 300 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_transpose", ins := [100, 901], outs := [300], params := [1, 2] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = transposeAxes 1 2 ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.smGraph) smStore 100) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hPm0_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 3000 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [1000, 910], outs := [3000], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = transposeAxes 1 2 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_transpose", ins := [1000, 910], outs := [3000], params := [1, 2] } 3000
      (fun t => transposeAxes 1 2 (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.pmGraph t 0 1000 910 3000 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_transpose", ins := [1000, 910], outs := [3000], params := [1, 2] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1000) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hPm0_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 3001 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 1, op := "OpName.BW_transpose", ins := [1001, 911], outs := [3001], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3001 = transposeAxes 1 2 (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 1, op := "OpName.BW_transpose", ins := [1001, 911], outs := [3001], params := [1, 2] } 3001
      (fun t => transposeAxes 1 2 (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.pmGraph t 1 1001 911 3001 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_transpose", ins := [1001, 911], outs := [3001], params := [1, 2] } :: (segment_000000_pm_nodes.drop 3)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3001 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1001) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hPm0_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 3002 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 2, op := "OpName.BW_transpose", ins := [1002, 912], outs := [3002], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3002 = transposeAxes 1 2 (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 2, op := "OpName.BW_transpose", ins := [1002, 912], outs := [3002], params := [1, 2] } 3002
      (fun t => transposeAxes 1 2 (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.pmGraph t 2 1002 912 3002 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.BW_transpose", ins := [1002, 912], outs := [3002], params := [1, 2] } :: (segment_000000_pm_nodes.drop 5)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3002 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1002) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hPm0_3 (pmStore : Store) : (segment_000000_pm_final pmStore) 3003 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1003) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 6) ++ [{ rank := 3, op := "OpName.BW_transpose", ins := [1003, 913], outs := [3003], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3003 = transposeAxes 1 2 (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) (segment_000000_pm_nodes.drop 7)
      { rank := 3, op := "OpName.BW_transpose", ins := [1003, 913], outs := [3003], params := [1, 2] } 3003
      (fun t => transposeAxes 1 2 (t 1003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.pmGraph t 3 1003 913 3003 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 3, op := "OpName.BW_transpose", ins := [1003, 913], outs := [3003], params := [1, 2] } :: (segment_000000_pm_nodes.drop 7)) 1003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3003 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1003) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 1003) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 1003) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hPm1_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 4000 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4000], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [(((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2000, (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2001, (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2002, (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2003] 1 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4000], params := [1, 2] } 4000
      (fun t => allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [(t) 2000, (t) 2001, (t) 2002, (t) 2003] 1 2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out TransposeAllToAll.pmGraph t 0 [2000, 2001, 2002, 2003] 4000 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4000], params := [1, 2] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4000], params := [1, 2] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4000], params := [1, 2] } :: (segment_000000_pm_nodes.drop 2)) 2002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4000], params := [1, 2] } :: (segment_000000_pm_nodes.drop 2)) 2003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by
    calc
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [(((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2000, (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2001, (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2002, (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2003] 1 2 := hout_prefix
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPm1_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 4001 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4001], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [(((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2000, (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2001, (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2002, (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2003] 1 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4001], params := [1, 2] } 4001
      (fun t => allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [(t) 2000, (t) 2001, (t) 2002, (t) 2003] 1 2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out TransposeAllToAll.pmGraph t 1 [2000, 2001, 2002, 2003] 4001 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4001], params := [1, 2] } :: (segment_000000_pm_nodes.drop 4)) 2000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4001], params := [1, 2] } :: (segment_000000_pm_nodes.drop 4)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4001], params := [1, 2] } :: (segment_000000_pm_nodes.drop 4)) 2002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4001], params := [1, 2] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by
    calc
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [(((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2000, (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2001, (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2002, (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2003] 1 2 := hout_prefix
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPm1_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 4002 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4002], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [(((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2000, (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2001, (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2002, (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2003] 1 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4002], params := [1, 2] } 4002
      (fun t => allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [(t) 2000, (t) 2001, (t) 2002, (t) 2003] 1 2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out TransposeAllToAll.pmGraph t 2 [2000, 2001, 2002, 2003] 4002 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4002], params := [1, 2] } :: (segment_000000_pm_nodes.drop 6)) 2000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4002], params := [1, 2] } :: (segment_000000_pm_nodes.drop 6)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4002], params := [1, 2] } :: (segment_000000_pm_nodes.drop 6)) 2002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4002], params := [1, 2] } :: (segment_000000_pm_nodes.drop 6)) 2003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by
    calc
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [(((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2000, (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2001, (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2002, (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2003] 1 2 := hout_prefix
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPm1_3 (pmStore : Store) : (segment_000000_pm_final pmStore) 4003 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4003], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4003 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [(((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2000, (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2001, (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2002, (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2003] 1 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 3, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4003], params := [1, 2] } 4003
      (fun t => allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [(t) 2000, (t) 2001, (t) 2002, (t) 2003] 1 2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out TransposeAllToAll.pmGraph t 3 [2000, 2001, 2002, 2003] 4003 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4003], params := [1, 2] } :: (segment_000000_pm_nodes.drop 8)) 2000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4003], params := [1, 2] } :: (segment_000000_pm_nodes.drop 8)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4003], params := [1, 2] } :: (segment_000000_pm_nodes.drop 8)) 2002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [2000, 2001, 2002, 2003], outs := [4003], params := [1, 2] } :: (segment_000000_pm_nodes.drop 8)) 2003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4003 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by
    calc
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [(((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2000, (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2001, (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2002, (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 2003] 1 2 := hout_prefix
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [((segment_000000_pm_final pmStore)) 2000, ((segment_000000_pm_final pmStore)) 2001, ((segment_000000_pm_final pmStore)) 2002, ((segment_000000_pm_final pmStore)) 2003] 1 2 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPm2_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 6000 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 8) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6000], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 6000 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [(((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5000, (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5001, (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5002, (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5003] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) (segment_000000_pm_nodes.drop 9)
      { rank := 0, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6000], params := [2, 1] } 6000
      (fun t => allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [(t) 5000, (t) 5001, (t) 5002, (t) 5003] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out TransposeAllToAll.pmGraph t 0 [5000, 5001, 5002, 5003] 6000 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5000 = (segment_000000_pm_final pmStore) 5000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6000], params := [2, 1] } :: (segment_000000_pm_nodes.drop 9)) 5000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5001 = (segment_000000_pm_final pmStore) 5001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6000], params := [2, 1] } :: (segment_000000_pm_nodes.drop 9)) 5001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5002 = (segment_000000_pm_final pmStore) 5002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6000], params := [2, 1] } :: (segment_000000_pm_nodes.drop 9)) 5002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5003 = (segment_000000_pm_final pmStore) 5003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6000], params := [2, 1] } :: (segment_000000_pm_nodes.drop 9)) 5003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 6000 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by
    calc
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [(((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5000, (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5001, (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5002, (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5003] 2 1 := hout_prefix
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 0 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPm2_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 6001 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 10) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6001], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 11) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 6001 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [(((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5000, (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5001, (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5002, (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5003] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 10) (segment_000000_pm_nodes.drop 11)
      { rank := 1, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6001], params := [2, 1] } 6001
      (fun t => allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [(t) 5000, (t) 5001, (t) 5002, (t) 5003] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out TransposeAllToAll.pmGraph t 1 [5000, 5001, 5002, 5003] 6001 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5000 = (segment_000000_pm_final pmStore) 5000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 10) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6001], params := [2, 1] } :: (segment_000000_pm_nodes.drop 11)) 5000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5001 = (segment_000000_pm_final pmStore) 5001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 10) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6001], params := [2, 1] } :: (segment_000000_pm_nodes.drop 11)) 5001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5002 = (segment_000000_pm_final pmStore) 5002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 10) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6001], params := [2, 1] } :: (segment_000000_pm_nodes.drop 11)) 5002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5003 = (segment_000000_pm_final pmStore) 5003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 10) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6001], params := [2, 1] } :: (segment_000000_pm_nodes.drop 11)) 5003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 6001 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by
    calc
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [(((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5000, (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5001, (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5002, (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5003] 2 1 := hout_prefix
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 1 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPm2_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 6002 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 12) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6002], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 13) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 6002 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [(((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5000, (((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5001, (((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5002, (((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5003] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 12) (segment_000000_pm_nodes.drop 13)
      { rank := 2, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6002], params := [2, 1] } 6002
      (fun t => allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [(t) 5000, (t) 5001, (t) 5002, (t) 5003] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out TransposeAllToAll.pmGraph t 2 [5000, 5001, 5002, 5003] 6002 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5000 = (segment_000000_pm_final pmStore) 5000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 12) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6002], params := [2, 1] } :: (segment_000000_pm_nodes.drop 13)) 5000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5001 = (segment_000000_pm_final pmStore) 5001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 12) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6002], params := [2, 1] } :: (segment_000000_pm_nodes.drop 13)) 5001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5002 = (segment_000000_pm_final pmStore) 5002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 12) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6002], params := [2, 1] } :: (segment_000000_pm_nodes.drop 13)) 5002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5003 = (segment_000000_pm_final pmStore) 5003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 12) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6002], params := [2, 1] } :: (segment_000000_pm_nodes.drop 13)) 5003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 6002 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by
    calc
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [(((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5000, (((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5001, (((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5002, (((segment_000000_pm_nodes.take 12)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5003] 2 1 := hout_prefix
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 2 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPm2_3 (pmStore : Store) : (segment_000000_pm_final pmStore) 6003 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 14) ++ [{ rank := 3, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6003], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 15) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 6003 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [(((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5000, (((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5001, (((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5002, (((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5003] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 14) (segment_000000_pm_nodes.drop 15)
      { rank := 3, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6003], params := [2, 1] } 6003
      (fun t => allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [(t) 5000, (t) 5001, (t) 5002, (t) 5003] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out TransposeAllToAll.pmGraph t 3 [5000, 5001, 5002, 5003] 6003 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5000 = (segment_000000_pm_final pmStore) 5000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 14) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6003], params := [2, 1] } :: (segment_000000_pm_nodes.drop 15)) 5000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5001 = (segment_000000_pm_final pmStore) 5001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 14) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6003], params := [2, 1] } :: (segment_000000_pm_nodes.drop 15)) 5001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5002 = (segment_000000_pm_final pmStore) 5002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 14) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6003], params := [2, 1] } :: (segment_000000_pm_nodes.drop 15)) 5002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 5003 = (segment_000000_pm_final pmStore) 5003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 14) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [5000, 5001, 5002, 5003], outs := [6003], params := [2, 1] } :: (segment_000000_pm_nodes.drop 15)) 5003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 6003 = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by
    calc
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [(((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5000, (((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5001, (((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5002, (((segment_000000_pm_nodes.take 14)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore) 5003] 2 1 := hout_prefix
      _ = allToAllPrimWithDims TransposeAllToAll.pmGraph.numRanks 3 [((segment_000000_pm_final pmStore)) 5000, ((segment_000000_pm_final pmStore)) 5001, ((segment_000000_pm_final pmStore)) 5002, ((segment_000000_pm_final pmStore)) 5003] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hSm3 (smStore : Store) : (segment_000000_sm_final smStore) 400 = transposeAxes 2 3 ((segment_000000_sm_final smStore) 200) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [200, 900], outs := [400], params := [2, 3] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = transposeAxes 2 3 (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TransposeAllToAll.smGraph) smStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_transpose", ins := [200, 900], outs := [400], params := [2, 3] } 400
      (fun t => transposeAxes 2 3 (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.smGraph t 0 200 900 400 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TransposeAllToAll.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_transpose", ins := [200, 900], outs := [400], params := [2, 3] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = transposeAxes 2 3 ((segment_000000_sm_final smStore) 200) := by
    calc
      _ = transposeAxes 2 3 (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TransposeAllToAll.smGraph) smStore 200) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000000_sm_final smStore) 200) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hPm3_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 7000 = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 9) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [4000, 920], outs := [7000], params := [2, 3] }] ++ (segment_000000_pm_nodes.drop 10) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7000 = transposeAxes 2 3 (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 9) (segment_000000_pm_nodes.drop 10)
      { rank := 0, op := "OpName.BW_transpose", ins := [4000, 920], outs := [7000], params := [2, 3] } 7000
      (fun t => transposeAxes 2 3 (t 4000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.pmGraph t 0 4000 920 7000 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4000 = (segment_000000_pm_final pmStore) 4000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 0, op := "OpName.BW_transpose", ins := [4000, 920], outs := [7000], params := [2, 3] } :: (segment_000000_pm_nodes.drop 10)) 4000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7000 = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4000) := by
    calc
      _ = transposeAxes 2 3 (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4000) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4000) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hPm3_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 7001 = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 11) ++ [{ rank := 1, op := "OpName.BW_transpose", ins := [4001, 921], outs := [7001], params := [2, 3] }] ++ (segment_000000_pm_nodes.drop 12) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7001 = transposeAxes 2 3 (((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 11) (segment_000000_pm_nodes.drop 12)
      { rank := 1, op := "OpName.BW_transpose", ins := [4001, 921], outs := [7001], params := [2, 3] } 7001
      (fun t => transposeAxes 2 3 (t 4001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.pmGraph t 1 4001 921 7001 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4001 = (segment_000000_pm_final pmStore) 4001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 11) ({ rank := 1, op := "OpName.BW_transpose", ins := [4001, 921], outs := [7001], params := [2, 3] } :: (segment_000000_pm_nodes.drop 12)) 4001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7001 = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4001) := by
    calc
      _ = transposeAxes 2 3 (((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4001) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4001) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hPm3_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 7002 = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 13) ++ [{ rank := 2, op := "OpName.BW_transpose", ins := [4002, 922], outs := [7002], params := [2, 3] }] ++ (segment_000000_pm_nodes.drop 14) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7002 = transposeAxes 2 3 (((segment_000000_pm_nodes.take 13)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 13) (segment_000000_pm_nodes.drop 14)
      { rank := 2, op := "OpName.BW_transpose", ins := [4002, 922], outs := [7002], params := [2, 3] } 7002
      (fun t => transposeAxes 2 3 (t 4002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.pmGraph t 2 4002 922 7002 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 13)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4002 = (segment_000000_pm_final pmStore) 4002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 13) ({ rank := 2, op := "OpName.BW_transpose", ins := [4002, 922], outs := [7002], params := [2, 3] } :: (segment_000000_pm_nodes.drop 14)) 4002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7002 = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4002) := by
    calc
      _ = transposeAxes 2 3 (((segment_000000_pm_nodes.take 13)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4002) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4002) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hPm3_3 (pmStore : Store) : (segment_000000_pm_final pmStore) 7003 = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4003) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 15) ++ [{ rank := 3, op := "OpName.BW_transpose", ins := [4003, 923], outs := [7003], params := [2, 3] }] ++ (segment_000000_pm_nodes.drop 16) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7003 = transposeAxes 2 3 (((segment_000000_pm_nodes.take 15)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 15) (segment_000000_pm_nodes.drop 16)
      { rank := 3, op := "OpName.BW_transpose", ins := [4003, 923], outs := [7003], params := [2, 3] } 7003
      (fun t => transposeAxes 2 3 (t 4003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TransposeAllToAll.pmGraph t 3 4003 923 7003 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 15)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4003 = (segment_000000_pm_final pmStore) 4003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TransposeAllToAll.pmGraph pmStore
      (segment_000000_pm_nodes.take 15) ({ rank := 3, op := "OpName.BW_transpose", ins := [4003, 923], outs := [7003], params := [2, 3] } :: (segment_000000_pm_nodes.drop 16)) 4003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7003 = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4003) := by
    calc
      _ = transposeAxes 2 3 (((segment_000000_pm_nodes.take 15)).foldl (applyNodeDistributedFaithful TransposeAllToAll.pmGraph) pmStore 4003) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000000_pm_final pmStore) 4003) := by rw [hout_read_0]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : before.Holds smStore pmStore) : after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hin0 : input_t.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 1 [2, 3 * [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003].length, 20, 7] [2, 3, 20, 7] at hin0
  have hws0 : smFinal 300 = transposeAxes 1 2 (smFinal 100) := segment_000000_hSm0 smStore
  have hwp0_0 : pmFinal 3000 = transposeAxes 1 2 (pmFinal 1000) := segment_000000_hPm0_0 pmStore
  have hwp0_1 : pmFinal 3001 = transposeAxes 1 2 (pmFinal 1001) := segment_000000_hPm0_1 pmStore
  have hwp0_2 : pmFinal 3002 = transposeAxes 1 2 (pmFinal 1002) := segment_000000_hPm0_2 pmStore
  have hwp0_3 : pmFinal 3003 = transposeAxes 1 2 (pmFinal 1003) := segment_000000_hPm0_3 pmStore
  have ht0 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim1_to_dim2_rank4 hin0
  have hOut0 : out_t.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 2 [2, 20, 12, 7] [2, 20, 3, 7]
    rw [hws0, hwp0_0, hwp0_1, hwp0_2, hwp0_3]
    simpa using ht0
  have hin1 : input_a.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 [2, 3 * [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003].length, 20, 7] [2, 3, 20, 7] at hin1
  have hpa := hin1
  have hwa0 := segment_000000_hPm1_0 pmStore
  change pmFinal 4000 = allToAllPrimWithDims 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 2 at hwa0
  have hwa1 := segment_000000_hPm1_1 pmStore
  change pmFinal 4001 = allToAllPrimWithDims 4 1 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 2 at hwa1
  have hwa2 := segment_000000_hPm1_2 pmStore
  change pmFinal 4002 = allToAllPrimWithDims 4 2 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 2 at hwa2
  have hwa3 := segment_000000_hPm1_3 pmStore
  change pmFinal 4003 = allToAllPrimWithDims 4 3 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 2 at hwa3
  have hHead : (([pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003].head?.map (fun t => t.shape)).getD []) = [2, 3, 20, 7] := by
    exact hpa.shard_shapes _ (by simp)
  have hpaValue : smFinal 200 = allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] := by simpa only [List.length_cons, List.length_nil] using hpa.full_value
  have hGatherShape : (allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003]).shape = [2, 12, 20, 7] := by
    rw [← hpaValue]; exact hpa.full_shape
  have hOdim : 2 < (allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003]).shape.length := by rw [hGatherShape]; native_decide
  have hDiv : (allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003]).shape.getD 2 0 % 4 = 0 := by rw [hGatherShape]; native_decide
  have hAShape0 : (pmFinal 4000).shape = [2, 12, 5, 7] := by
    rw [hwa0, allToAllPrimWithDims_shape 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 2 [2, 3, 20, 7] hHead (by native_decide)]
    native_decide
  have hAShape1 : (pmFinal 4001).shape = [2, 12, 5, 7] := by
    rw [hwa1, allToAllPrimWithDims_shape 4 1 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 2 [2, 3, 20, 7] hHead (by native_decide)]
    native_decide
  have hAShape2 : (pmFinal 4002).shape = [2, 12, 5, 7] := by
    rw [hwa2, allToAllPrimWithDims_shape 4 2 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 2 [2, 3, 20, 7] hHead (by native_decide)]
    native_decide
  have hAShape3 : (pmFinal 4003).shape = [2, 12, 5, 7] := by
    rw [hwa3, allToAllPrimWithDims_shape 4 3 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 2 [2, 3, 20, 7] hHead (by native_decide)]
    native_decide
  have hOrdered : [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] = List.ofFn (fun r : Fin 4 => allToAllPrimWithDims 4 r.1 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 2) := by
    rw [hwa0, hwa1, hwa2, hwa3]
    rfl
  have hcomm := TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 2 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] (by simp) hOdim hDiv
  have hcommExact : allGatherPrimDimN 2 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003].length 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] = allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] := by
    rw [hOrdered]
    simpa only [List.length_cons, List.length_nil, List.length_ofFn] using hcomm
  have hOut1 : out_a.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 200) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 [2, 12, 20, 7] [2, 12, 5, 7]
    refine { full_value := ?_, full_shape := hpa.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide }
    · rw [hcommExact]
      exact hpaValue
    · intro shard hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2 | h3
      · subst shard
        exact hAShape0
      · subst shard
        exact hAShape1
      · subst shard
        exact hAShape2
      · subst shard
        exact hAShape3
  have hin2 : input_b.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 500) [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 [2, 12, 5 * [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003].length, 7] [2, 12, 5, 7] at hin2
  have hpa := hin2
  have hwa0 := segment_000000_hPm2_0 pmStore
  change pmFinal 6000 = allToAllPrimWithDims 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 1 at hwa0
  have hwa1 := segment_000000_hPm2_1 pmStore
  change pmFinal 6001 = allToAllPrimWithDims 4 1 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 1 at hwa1
  have hwa2 := segment_000000_hPm2_2 pmStore
  change pmFinal 6002 = allToAllPrimWithDims 4 2 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 1 at hwa2
  have hwa3 := segment_000000_hPm2_3 pmStore
  change pmFinal 6003 = allToAllPrimWithDims 4 3 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 1 at hwa3
  have hHead : (([pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003].head?.map (fun t => t.shape)).getD []) = [2, 12, 5, 7] := by
    exact hpa.shard_shapes _ (by simp)
  have hpaValue : smFinal 500 = allGatherPrimDimN 2 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] := by simpa only [List.length_cons, List.length_nil] using hpa.full_value
  have hGatherShape : (allGatherPrimDimN 2 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003]).shape = [2, 12, 20, 7] := by
    rw [← hpaValue]; exact hpa.full_shape
  have hOdim : 1 < (allGatherPrimDimN 2 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003]).shape.length := by rw [hGatherShape]; native_decide
  have hDiv : (allGatherPrimDimN 2 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003]).shape.getD 1 0 % 4 = 0 := by rw [hGatherShape]; native_decide
  have hAShape0 : (pmFinal 6000).shape = [2, 3, 20, 7] := by
    rw [hwa0, allToAllPrimWithDims_shape 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 1 [2, 12, 5, 7] hHead (by native_decide)]
    native_decide
  have hAShape1 : (pmFinal 6001).shape = [2, 3, 20, 7] := by
    rw [hwa1, allToAllPrimWithDims_shape 4 1 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 1 [2, 12, 5, 7] hHead (by native_decide)]
    native_decide
  have hAShape2 : (pmFinal 6002).shape = [2, 3, 20, 7] := by
    rw [hwa2, allToAllPrimWithDims_shape 4 2 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 1 [2, 12, 5, 7] hHead (by native_decide)]
    native_decide
  have hAShape3 : (pmFinal 6003).shape = [2, 3, 20, 7] := by
    rw [hwa3, allToAllPrimWithDims_shape 4 3 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 1 [2, 12, 5, 7] hHead (by native_decide)]
    native_decide
  have hOrdered : [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003] = List.ofFn (fun r : Fin 4 => allToAllPrimWithDims 4 r.1 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 2 1) := by
    rw [hwa0, hwa1, hwa2, hwa3]
    rfl
  have hcomm := TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 2 1 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] (by simp) hOdim hDiv
  have hcommExact : allGatherPrimDimN 1 [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003].length 0 [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003] = allGatherPrimDimN 2 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] := by
    rw [hOrdered]
    simpa only [List.length_cons, List.length_nil, List.length_ofFn] using hcomm
  have hOut2 : out_b.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 500) [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003] 1 [2, 12, 20, 7] [2, 3, 20, 7]
    refine { full_value := ?_, full_shape := hpa.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide }
    · rw [hcommExact]
      exact hpaValue
    · intro shard hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2 | h3
      · subst shard
        exact hAShape0
      · subst shard
        exact hAShape1
      · subst shard
        exact hAShape2
      · subst shard
        exact hAShape3
  have hin3 : out_a.Holds smFinal pmFinal := hOut1
  change ShardedRel (smFinal 200) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 [2, 12, 5 * [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003].length, 7] [2, 12, 5, 7] at hin3
  have hws3 : smFinal 400 = transposeAxes 2 3 (smFinal 200) := segment_000000_hSm3 smStore
  have hwp3_0 : pmFinal 7000 = transposeAxes 2 3 (pmFinal 4000) := segment_000000_hPm3_0 pmStore
  have hwp3_1 : pmFinal 7001 = transposeAxes 2 3 (pmFinal 4001) := segment_000000_hPm3_1 pmStore
  have hwp3_2 : pmFinal 7002 = transposeAxes 2 3 (pmFinal 4002) := segment_000000_hPm3_2 pmStore
  have hwp3_3 : pmFinal 7003 = transposeAxes 2 3 (pmFinal 4003) := segment_000000_hPm3_3 pmStore
  have ht3 := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4 hin3
  have hOut3 : out_c.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 400) [pmFinal 7000, pmFinal 7001, pmFinal 7002, pmFinal 7003] 3 [2, 12, 7, 20] [2, 12, 7, 5]
    rw [hws3, hwp3_0, hwp3_1, hwp3_2, hwp3_3]
    simpa using ht3
  intro fact hfact
  have covered : fact ∈ [out_t, out_a, out_b, out_c] ++ before.facts := by
    exact (show after.facts ⊆ [out_t, out_a, out_b, out_c] ++ before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl | rfl | rfl
    · exact hOut0
    · exact hOut1
    · exact hOut2
    · exact hOut3
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate TransposeAllToAll.smGraph TransposeAllToAll.pmGraph before after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro smStore pmStore hstate; have h := segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end TransposeAllToAll
