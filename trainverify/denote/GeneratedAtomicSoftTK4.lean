import denote.RelationCompiler
import denote.KRankBWSoftmaxGeneral
import denote.RelationCompiler
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace BWSoftmaxTranspose
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300] }, { rank := 0, op := "OpName.BW_transpose", ins := [400, 99], outs := [500], params := [1, 2] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000] }, { rank := 0, op := "OpName.BW_transpose", ins := [4000, 99], outs := [5000], params := [1, 2] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001] }, { rank := 1, op := "OpName.BW_transpose", ins := [4001, 99], outs := [5001], params := [1, 2] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002] }, { rank := 2, op := "OpName.BW_transpose", ins := [4002, 99], outs := [5002], params := [1, 2] }, { rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003] }, { rank := 3, op := "OpName.BW_transpose", ins := [4003, 99], outs := [5003], params := [1, 2] }] }
def fg : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 1 [2, 12, 5, 7] [2, 3, 5, 7]
def fx : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 1 [2, 12, 5, 7] [2, 3, 5, 7]
def fti : RelationFact := .sharded 400 [4000, 4001, 4002, 4003] 2 [2, 3, 20, 7] [2, 3, 5, 7]
def fo : RelationFact := .sharded 300 [3000, 3001, 3002, 3003] 1 [2, 12, 5, 7] [2, 3, 5, 7]
def fto : RelationFact := .sharded 500 [5000, 5001, 5002, 5003] 1 [2, 20, 3, 7] [2, 5, 3, 7]
def state_000000 : RelationState where
  facts := [fg, fx, fti]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fg, fx, fti, fo, fto]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300] }, { rank := 0, op := "OpName.BW_transpose", ins := [400, 99], outs := [500], params := [1, 2] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000] }, { rank := 0, op := "OpName.BW_transpose", ins := [4000, 99], outs := [5000], params := [1, 2] }, { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001] }, { rank := 1, op := "OpName.BW_transpose", ins := [4001, 99], outs := [5001], params := [1, 2] }, { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002] }, { rank := 2, op := "OpName.BW_transpose", ins := [4002, 99], outs := [5002], params := [1, 2] }, { rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003] }, { rank := 3, op := "OpName.BW_transpose", ins := [4003, 99], outs := [5003], params := [1, 2] }]
private def segment_000000_sm_final (z : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) z
private def segment_000000_pm_final (z : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) z

private theorem segment_000000_hTransposeSm (smStore : Store) : (segment_000000_sm_final smStore) 500 = transposeAxes 1 2 ((segment_000000_sm_final smStore) 400) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [400, 99], outs := [500], params := [1, 2] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 500 = transposeAxes 1 2 (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore 400) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_transpose", ins := [400, 99], outs := [500], params := [1, 2] } 500
      (fun t => transposeAxes 1 2 (t 400)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out BWSoftmaxTranspose.smGraph t 0 400 99 500 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore 400 = (segment_000000_sm_final smStore) 400 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_transpose", ins := [400, 99], outs := [500], params := [1, 2] } :: (segment_000000_sm_nodes.drop 2)) 400
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 500 = transposeAxes 1 2 ((segment_000000_sm_final smStore) 400) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore 400) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_sm_final smStore) 400) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hSoftmaxSm (smStore : Store) : (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = bw_softmax (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300] } 300
      (fun t => bw_softmax (t 100) (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxTranspose.smGraph t 0 100 200 300 []
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by
    calc
      _ = bw_softmax (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.smGraph) smStore 200) := hout_prefix
      _ = bw_softmax ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hTransposePm0 (pmStore : Store) : (segment_000000_pm_final pmStore) 5000 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [4000, 99], outs := [5000], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = transposeAxes 1 2 (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_transpose", ins := [4000, 99], outs := [5000], params := [1, 2] } 5000
      (fun t => transposeAxes 1 2 (t 4000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out BWSoftmaxTranspose.pmGraph t 0 4000 99 5000 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4000 = (segment_000000_pm_final pmStore) 4000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_transpose", ins := [4000, 99], outs := [5000], params := [1, 2] } :: (segment_000000_pm_nodes.drop 2)) 4000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4000) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4000) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4000) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hTransposePm1 (pmStore : Store) : (segment_000000_pm_final pmStore) 5001 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_transpose", ins := [4001, 99], outs := [5001], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = transposeAxes 1 2 (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_transpose", ins := [4001, 99], outs := [5001], params := [1, 2] } 5001
      (fun t => transposeAxes 1 2 (t 4001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out BWSoftmaxTranspose.pmGraph t 1 4001 99 5001 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4001 = (segment_000000_pm_final pmStore) 4001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_transpose", ins := [4001, 99], outs := [5001], params := [1, 2] } :: (segment_000000_pm_nodes.drop 4)) 4001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4001) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4001) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4001) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hTransposePm2 (pmStore : Store) : (segment_000000_pm_final pmStore) 5002 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_transpose", ins := [4002, 99], outs := [5002], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = transposeAxes 1 2 (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_transpose", ins := [4002, 99], outs := [5002], params := [1, 2] } 5002
      (fun t => transposeAxes 1 2 (t 4002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out BWSoftmaxTranspose.pmGraph t 2 4002 99 5002 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4002 = (segment_000000_pm_final pmStore) 4002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_transpose", ins := [4002, 99], outs := [5002], params := [1, 2] } :: (segment_000000_pm_nodes.drop 6)) 4002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4002) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4002) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4002) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hTransposePm3 (pmStore : Store) : (segment_000000_pm_final pmStore) 5003 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4003) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_transpose", ins := [4003, 99], outs := [5003], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5003 = transposeAxes 1 2 (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_transpose", ins := [4003, 99], outs := [5003], params := [1, 2] } 5003
      (fun t => transposeAxes 1 2 (t 4003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out BWSoftmaxTranspose.pmGraph t 3 4003 99 5003 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4003 = (segment_000000_pm_final pmStore) 4003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_transpose", ins := [4003, 99], outs := [5003], params := [1, 2] } :: (segment_000000_pm_nodes.drop 8)) 4003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5003 = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4003) := by
    calc
      _ = transposeAxes 1 2 (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 4003) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000000_pm_final pmStore) 4003) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hSoftmaxPm0 (pmStore : Store) : (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = bw_softmax (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000] } 3000
      (fun t => bw_softmax (t 1000) (t 2000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxTranspose.pmGraph t 0 1000 2000 3000 []
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_softmax", ins := [1000, 2000], outs := [3000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2000) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hSoftmaxPm1 (pmStore : Store) : (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3001 = bw_softmax (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001] } 3001
      (fun t => bw_softmax (t 1001) (t 2001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxTranspose.pmGraph t 1 1001 2001 3001 []
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001] } :: (segment_000000_pm_nodes.drop 3)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_softmax", ins := [1001, 2001], outs := [3001] } :: (segment_000000_pm_nodes.drop 3)) 2001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3001 = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2001) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hSoftmaxPm2 (pmStore : Store) : (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3002 = bw_softmax (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002] } 3002
      (fun t => bw_softmax (t 1002) (t 2002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxTranspose.pmGraph t 2 1002 2002 3002 []
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002] } :: (segment_000000_pm_nodes.drop 5)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.BW_softmax", ins := [1002, 2002], outs := [3002] } :: (segment_000000_pm_nodes.drop 5)) 2002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3002 = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2002) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hSoftmaxPm3 (pmStore : Store) : (segment_000000_pm_final pmStore) 3003 = bw_softmax ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 6) ++ [{ rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003] }] ++ (segment_000000_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3003 = bw_softmax (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) (segment_000000_pm_nodes.drop 7)
      { rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003] } 3003
      (fun t => bw_softmax (t 1003) (t 2003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 BWSoftmaxTranspose.pmGraph t 3 1003 2003 3003 []
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003] } :: (segment_000000_pm_nodes.drop 7)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSoftmaxTranspose.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 3, op := "OpName.BW_softmax", ins := [1003, 2003], outs := [3003] } :: (segment_000000_pm_nodes.drop 7)) 2003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3003 = bw_softmax ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWSoftmaxTranspose.pmGraph) pmStore 2003) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) := by rw [hout_read_0, hout_read_1]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_000000.Holds smStore pmStore) : state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
    let smFinal := segment_000000_sm_final smStore
    let pmFinal := segment_000000_pm_final pmStore
    have hframe : state_000000.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hti : fti.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 [2, 3, 5 * [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003].length, 7] [2, 3, 5, 7] at hti
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 1 [2, 12, 5, 7] [2, 3, 5, 7] at hg
    have hy : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 [2, 12, 5, 7] [2, 3, 5, 7] at hy
    have hTsm := segment_000000_hTransposeSm smStore
    change smFinal 500 = transposeAxes 1 2 (smFinal 400) at hTsm
    have hSsm := segment_000000_hSoftmaxSm smStore
    change smFinal 300 = bw_softmax (smFinal 100) (smFinal 200) at hSsm
    have hTpm0 := segment_000000_hTransposePm0 pmStore
    change pmFinal 5000 = transposeAxes 1 2 (pmFinal 4000) at hTpm0
    have hSpm0 := segment_000000_hSoftmaxPm0 pmStore
    change pmFinal 3000 = bw_softmax (pmFinal 1000) (pmFinal 2000) at hSpm0
    have hgShape0 := hg.shard_shapes (pmFinal 1000) (by simp)
    have hyShape0 := hy.shard_shapes (pmFinal 2000) (by simp)
    have hSShape0 : (pmFinal 3000).shape = [2, 3, 5, 7] := by rw [hSpm0]; exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 hyShape0
    have hTpm1 := segment_000000_hTransposePm1 pmStore
    change pmFinal 5001 = transposeAxes 1 2 (pmFinal 4001) at hTpm1
    have hSpm1 := segment_000000_hSoftmaxPm1 pmStore
    change pmFinal 3001 = bw_softmax (pmFinal 1001) (pmFinal 2001) at hSpm1
    have hgShape1 := hg.shard_shapes (pmFinal 1001) (by simp)
    have hyShape1 := hy.shard_shapes (pmFinal 2001) (by simp)
    have hSShape1 : (pmFinal 3001).shape = [2, 3, 5, 7] := by rw [hSpm1]; exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 hyShape1
    have hTpm2 := segment_000000_hTransposePm2 pmStore
    change pmFinal 5002 = transposeAxes 1 2 (pmFinal 4002) at hTpm2
    have hSpm2 := segment_000000_hSoftmaxPm2 pmStore
    change pmFinal 3002 = bw_softmax (pmFinal 1002) (pmFinal 2002) at hSpm2
    have hgShape2 := hg.shard_shapes (pmFinal 1002) (by simp)
    have hyShape2 := hy.shard_shapes (pmFinal 2002) (by simp)
    have hSShape2 : (pmFinal 3002).shape = [2, 3, 5, 7] := by rw [hSpm2]; exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 hyShape2
    have hTpm3 := segment_000000_hTransposePm3 pmStore
    change pmFinal 5003 = transposeAxes 1 2 (pmFinal 4003) at hTpm3
    have hSpm3 := segment_000000_hSoftmaxPm3 pmStore
    change pmFinal 3003 = bw_softmax (pmFinal 1003) (pmFinal 2003) at hSpm3
    have hgShape3 := hg.shard_shapes (pmFinal 1003) (by simp)
    have hyShape3 := hy.shard_shapes (pmFinal 2003) (by simp)
    have hSShape3 : (pmFinal 3003).shape = [2, 3, 5, 7] := by rw [hSpm3]; exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 hyShape3
    have htRaw := TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4 hti
    have houtT : fto.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 500) [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 1 [2, 20, 3, 7] [2, 5, 3, 7]
      rw [hTsm, hTpm0, hTpm1, hTpm2, hTpm3]
      simpa using htRaw
    have hgValue : smFinal 100 = allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] := by simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hyValue : smFinal 200 = allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] := by simpa only [List.length_cons, List.length_nil] using hy.full_value
    have hcomm := TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim1_rank4 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 4 2 3 5 7
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp) (by simp) hg.shard_shapes hy.shard_shapes
    have hSValue : smFinal 300 = allGatherPrimDimN 1 4 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] := by
      rw [hSsm, hgValue, hyValue, hcomm]
      simp only [List.zipWith]
      rw [← hSpm0, ← hSpm1, ← hSpm2, ← hSpm3]
    have hSValueList : smFinal 300 = allGatherPrimDimN 1 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003].length 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] := by simpa only [List.length_cons, List.length_nil] using hSValue
    have hSFullShape : (smFinal 300).shape = [2, 12, 5, 7] := by rw [hSsm]; exact bw_softmax_shape_g199 _ _ [2, 12, 5] 7 hy.full_shape
    have hSShapes : ∀ z ∈ [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003], z.shape = [2, 3, 5, 7] := by
      simp only [List.forall_mem_cons]
      exact ⟨hSShape0, hSShape1, hSShape2, hSShape3, List.forall_mem_nil _⟩
    have houtS : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 1 [2, 12, 5, 7] [2, 3, 5, 7]
      exact { full_value := hSValueList, full_shape := hSFullShape, shards_nonempty := List.cons_ne_nil _ _, gather_dim_lt := by native_decide, shard_shapes := hSShapes, shape_contract := by simp only [List.map, List.length_cons, List.length_nil]; native_decide }
    intro fact hfact
    have covered : fact ∈ [fto, fo] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fto, fo] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · exact houtT
      · exact houtS
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 : ClosedDepSegmentCertificate BWSoftmaxTranspose.smGraph BWSoftmaxTranspose.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro smStore pmStore hstate; exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end BWSoftmaxTranspose
