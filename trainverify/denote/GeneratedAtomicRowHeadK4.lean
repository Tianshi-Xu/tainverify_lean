import denote.RelationCompiler
import denote.KRankBWLinearDwRowGeneral
import denote.KRankBWLinearDxRow
import denote.KRankBWMatmulHead
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticRowHead
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] }, { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] }, { rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] }, { rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] }, { rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] }, { rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 2 [2, 5, 28] [2, 5, 7]
def fact_x : RelationFact := .joined 200 2000 [2, 5, 11]
def fact_w : RelationFact := .sharded 300 [3000, 3001, 3002, 3003] 0 [28, 11] [7, 11]
def fact_dw : RelationFact := .sharded 401 [5000, 5001, 5002, 5003] 0 [28, 11] [7, 11]
def fact_dx : RelationFact := .reduction 400 [4000, 4001, 4002, 4003] [2, 5, 11]
def mg : RelationFact := .sharded 600 [6000, 6001, 6002, 6003] 1 [2, 8, 3, 7] [2, 2, 3, 7]
def mx : RelationFact := .sharded 700 [7000, 7001, 7002, 7003] 1 [2, 8, 3, 5] [2, 2, 3, 5]
def my : RelationFact := .sharded 800 [8000, 8001, 8002, 8003] 1 [2, 8, 5, 7] [2, 2, 5, 7]
def mo0 : RelationFact := .sharded 900 [9000, 9001, 9002, 9003] 1 [2, 8, 3, 5] [2, 2, 3, 5]
def mo1 : RelationFact := .sharded 901 [10000, 10001, 10002, 10003] 1 [2, 8, 5, 7] [2, 2, 5, 7]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w, mg, mx, my]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_dw, fact_dx, mg, mx, my, mo0, mo1]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] }, { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] }, { rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] }, { rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] }, { rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] }, { rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] }]
private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) s
private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) s
private def segment_000000_row_post : RelationState where
  facts := [fact_g, fact_x, fact_w, mg, mx, my, fact_dw, fact_dx]
  nonempty := by decide
private theorem segment_000000_row_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 400 =
      (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_linear (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 200) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticRowHead.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 2)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 200) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_hSmDwWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 401 =
      (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_linear (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 200) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_linear (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticRowHead.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 2)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 200) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 4000 =
      (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticRowHead.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 4001 =
      (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3001)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1001) (t 2000) (t 3001)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticRowHead.pmGraph t 1 1001 2000 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3001)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 4002 =
      (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3002)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } 4002
      (fun t => (bw_linear (t 1002) (t 2000) (t 3002)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticRowHead.pmGraph t 2 1002 2000 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3002)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 4003 =
      (bw_linear ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3003)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4003 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3003)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } 4003
      (fun t => (bw_linear (t 1003) (t 2000) (t 3003)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticRowHead.pmGraph t 3 1003 2000 3003 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3003 = (segment_000000_pm_final pmStore) 3003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4003 = (bw_linear ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3003)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3003)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3003)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_hPmDwWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5000 =
      (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_linear (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticRowHead.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_hPmDwWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5001 =
      (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3001)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } 5001
      (fun t => (bw_linear (t 1001) (t 2000) (t 3001)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticRowHead.pmGraph t 1 1001 2000 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3001)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3001)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_hPmDwWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5002 =
      (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3002)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } 5002
      (fun t => (bw_linear (t 1002) (t 2000) (t 3002)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticRowHead.pmGraph t 2 1002 2000 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3002)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3002)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_hPmDwWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5003 =
      (bw_linear ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3003)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5003 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3003)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } 5003
      (fun t => (bw_linear (t 1003) (t 2000) (t 3003)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SyntheticRowHead.pmGraph t 3 1003 2000 3003 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3003 = (segment_000000_pm_final pmStore) 3003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2000, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5003 = (bw_linear ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3003)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 3003)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3003)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_row_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    segment_000000_row_post.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
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
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 2 [2, 5, 28] [2, 5, 7] at hg
    have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
    change smFinal 200 = pmFinal 2000 ∧
      (smFinal 200).shape = [2, 5, 11] ∧
      (pmFinal 2000).shape = [2, 5, 11] at hx
    have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 0 [28, 11] [7, 11] at hw
    have hgValue : smFinal 100 = allGatherPrimDimN 2 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hwValue : smFinal 300 = allGatherPrimDimN 0 4 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] := by
      simpa only [List.length_cons, List.length_nil] using hw.full_value
    have hSmWriter : smFinal 400 =
        (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).1 :=
      segment_000000_row_hSmWriter smStore
    have hSmDwWriter : smFinal 401 =
        (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).2 :=
      segment_000000_row_hSmDwWriter smStore
    have hPmWriter0 : pmFinal 4000 =
        (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1 :=
      segment_000000_row_hPmWriter0 pmStore
    have hPmDwWriter0 : pmFinal 5000 =
        (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2 :=
      segment_000000_row_hPmDwWriter0 pmStore
    have hgShape0 := hg.shard_shapes (pmFinal 1000) (by simp)
    have hwShape0 := hw.shard_shapes (pmFinal 3000) (by simp)
    have hOutShape0 : (pmFinal 4000).shape = [2, 5, 11] := by
      rw [hPmWriter0]
      exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _
        hgShape0 hx.2.2 hwShape0
    have hDwOutShape0 : (pmFinal 5000).shape = [7, 11] := by
      rw [hPmDwWriter0]
      exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _
        hgShape0 hx.2.2 hwShape0
    have hPmWriter1 : pmFinal 4001 =
        (bw_linear (pmFinal 1001) (pmFinal 2000) (pmFinal 3001)).1 :=
      segment_000000_row_hPmWriter1 pmStore
    have hPmDwWriter1 : pmFinal 5001 =
        (bw_linear (pmFinal 1001) (pmFinal 2000) (pmFinal 3001)).2 :=
      segment_000000_row_hPmDwWriter1 pmStore
    have hgShape1 := hg.shard_shapes (pmFinal 1001) (by simp)
    have hwShape1 := hw.shard_shapes (pmFinal 3001) (by simp)
    have hOutShape1 : (pmFinal 4001).shape = [2, 5, 11] := by
      rw [hPmWriter1]
      exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _
        hgShape1 hx.2.2 hwShape1
    have hDwOutShape1 : (pmFinal 5001).shape = [7, 11] := by
      rw [hPmDwWriter1]
      exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _
        hgShape1 hx.2.2 hwShape1
    have hPmWriter2 : pmFinal 4002 =
        (bw_linear (pmFinal 1002) (pmFinal 2000) (pmFinal 3002)).1 :=
      segment_000000_row_hPmWriter2 pmStore
    have hPmDwWriter2 : pmFinal 5002 =
        (bw_linear (pmFinal 1002) (pmFinal 2000) (pmFinal 3002)).2 :=
      segment_000000_row_hPmDwWriter2 pmStore
    have hgShape2 := hg.shard_shapes (pmFinal 1002) (by simp)
    have hwShape2 := hw.shard_shapes (pmFinal 3002) (by simp)
    have hOutShape2 : (pmFinal 4002).shape = [2, 5, 11] := by
      rw [hPmWriter2]
      exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _
        hgShape2 hx.2.2 hwShape2
    have hDwOutShape2 : (pmFinal 5002).shape = [7, 11] := by
      rw [hPmDwWriter2]
      exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _
        hgShape2 hx.2.2 hwShape2
    have hPmWriter3 : pmFinal 4003 =
        (bw_linear (pmFinal 1003) (pmFinal 2000) (pmFinal 3003)).1 :=
      segment_000000_row_hPmWriter3 pmStore
    have hPmDwWriter3 : pmFinal 5003 =
        (bw_linear (pmFinal 1003) (pmFinal 2000) (pmFinal 3003)).2 :=
      segment_000000_row_hPmDwWriter3 pmStore
    have hgShape3 := hg.shard_shapes (pmFinal 1003) (by simp)
    have hwShape3 := hw.shard_shapes (pmFinal 3003) (by simp)
    have hOutShape3 : (pmFinal 4003).shape = [2, 5, 11] := by
      rw [hPmWriter3]
      exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _
        hgShape3 hx.2.2 hwShape3
    have hDwOutShape3 : (pmFinal 5003).shape = [7, 11] := by
      rw [hPmDwWriter3]
      exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _
        hgShape3 hx.2.2 hwShape3
    have hcomm_raw := TrainVerify.Denote.bw_linear_dx_row_reduction_rank3 4 2 5 7 11
      [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] (pmFinal 2000)
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
      hg.shard_shapes hw.shard_shapes hx.2.2
    have hcomm : (bw_linear (allGatherPrimDimN 2 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003])
      (pmFinal 2000) (allGatherPrimDimN 0 4 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003])).1 =
      allReducePrim 4 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1, (bw_linear (pmFinal 1001) (pmFinal 2000) (pmFinal 3001)).1, (bw_linear (pmFinal 1002) (pmFinal 2000) (pmFinal 3002)).1, (bw_linear (pmFinal 1003) (pmFinal 2000) (pmFinal 3003)).1] := by
      simpa only [List.zipWith, tensorSum, allReducePrim, List.head?_cons, Option.map_some, Option.getD_some] using hcomm_raw
    have hOutValue : smFinal 400 = allReducePrim 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] := by
      rw [hSmWriter, hgValue, hx.1, hwValue, hcomm]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2, ← hPmWriter3]
    have hOutValueList : smFinal 400 =
        allReducePrim [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003].length 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 400).shape = [2, 5, 11] := by
      rw [hSmWriter]
      exact bw_linear_3d_fst_shape 2 5 28 11 _ _ _
        hg.full_shape hx.2.1 hw.full_shape
    have hout : fact_dx.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] [2, 5, 11]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        contributions_nonempty := by simp
        contribution_shapes := ?_
        reduced_shape := ?_
      }
      · intro contribution hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3
        · subst contribution
          exact hOutShape0
        · subst contribution
          exact hOutShape1
        · subst contribution
          exact hOutShape2
        · subst contribution
          exact hOutShape3
      · rw [← hOutValueList]
        exact hFullShape
    have hDwCommRaw := TrainVerify.Denote.bw_linear_dw_row_allGather_rank3 4 2 5 7 11
      [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] (pmFinal 2000)
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
      hg.shard_shapes hw.shard_shapes hx.2.2
    have hDwComm : (bw_linear (allGatherPrimDimN 2 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003])
        (pmFinal 2000) (allGatherPrimDimN 0 4 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003])).2 =
        allGatherPrimDimN 0 4 0 [(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2, (bw_linear (pmFinal 1001) (pmFinal 2000) (pmFinal 3001)).2, (bw_linear (pmFinal 1002) (pmFinal 2000) (pmFinal 3002)).2, (bw_linear (pmFinal 1003) (pmFinal 2000) (pmFinal 3003)).2] := by
      simpa only [List.zipWith] using hDwCommRaw
    have hDwValue : smFinal 401 = allGatherPrimDimN 0 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] := by
      rw [hSmDwWriter, hgValue, hx.1, hwValue, hDwComm]
      rw [← hPmDwWriter0, ← hPmDwWriter1, ← hPmDwWriter2, ← hPmDwWriter3]
    have hDwValueList : smFinal 401 = allGatherPrimDimN 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003].length 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] := by
      simpa only [List.length_cons, List.length_nil] using hDwValue
    have hDwFullShape : (smFinal 401).shape = [28, 11] := by
      rw [hSmDwWriter]
      exact bw_linear_3d_snd_shape 2 5 28 11 _ _ _
        hg.full_shape hx.2.1 hw.full_shape
    have houtDw : fact_dw.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 401) [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 0 [28, 11] [7, 11]
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
      rcases hmem with h0 | h1 | h2 | h3
      · subst shard
        exact hDwOutShape0
      · subst shard
        exact hDwOutShape1
      · subst shard
        exact hDwOutShape2
      · subst shard
        exact hDwOutShape3
    intro fact hfact
    have covered : fact ∈ [fact_dx, fact_dw] ++ state_before.facts := by
      exact (show segment_000000_row_post.facts ⊆ [fact_dx, fact_dw] ++ state_before.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · exact hout
      · exact houtDw
    · exact hframe fact old


private def segment_000000_head_post : RelationState where
  facts := [fact_g, fact_x, fact_w, mg, mx, my, mo0, mo1]
  nonempty := by decide
private theorem segment_000000_head_hSm0(smStore:Store):(segment_000000_sm_final smStore) 900=(bw_matmul ((segment_000000_sm_final smStore) 600) ((segment_000000_sm_final smStore) 700) ((segment_000000_sm_final smStore) 800)).1:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 900 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 600) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 700) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 800)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] } 900
      (fun t => (bw_matmul (t 600) (t 700) (t 800)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out SyntheticRowHead.smGraph t 0 600 700 800 900 901 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 600 = (segment_000000_sm_final smStore) 600 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] } :: (segment_000000_sm_nodes.drop 1)) 600
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 700 = (segment_000000_sm_final smStore) 700 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] } :: (segment_000000_sm_nodes.drop 1)) 700
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 800 = (segment_000000_sm_final smStore) 800 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] } :: (segment_000000_sm_nodes.drop 1)) 800
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 900 = (bw_matmul ((segment_000000_sm_final smStore) 600) ((segment_000000_sm_final smStore) 700) ((segment_000000_sm_final smStore) 800)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 600) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 700) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 800)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 600) ((segment_000000_sm_final smStore) 700) ((segment_000000_sm_final smStore) 800)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_hPm0_0(pmStore:Store):(segment_000000_pm_final pmStore) 9000=(bw_matmul ((segment_000000_pm_final pmStore) 6000) ((segment_000000_pm_final pmStore) 7000) ((segment_000000_pm_final pmStore) 8000)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 9000 = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] } 9000
      (fun t => (bw_matmul (t 6000) (t 7000) (t 8000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out SyntheticRowHead.pmGraph t 0 6000 7000 8000 9000 10000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6000 = (segment_000000_pm_final pmStore) 6000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] } :: (segment_000000_pm_nodes.drop 5)) 6000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7000 = (segment_000000_pm_final pmStore) 7000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] } :: (segment_000000_pm_nodes.drop 5)) 7000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8000 = (segment_000000_pm_final pmStore) 8000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] } :: (segment_000000_pm_nodes.drop 5)) 8000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 9000 = (bw_matmul ((segment_000000_pm_final pmStore) 6000) ((segment_000000_pm_final pmStore) 7000) ((segment_000000_pm_final pmStore) 8000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 6000) ((segment_000000_pm_final pmStore) 7000) ((segment_000000_pm_final pmStore) 8000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_hPm0_1(pmStore:Store):(segment_000000_pm_final pmStore) 9001=(bw_matmul ((segment_000000_pm_final pmStore) 6001) ((segment_000000_pm_final pmStore) 7001) ((segment_000000_pm_final pmStore) 8001)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 9001 = (bw_matmul (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6001) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7001) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8001)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] } 9001
      (fun t => (bw_matmul (t 6001) (t 7001) (t 8001)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out SyntheticRowHead.pmGraph t 1 6001 7001 8001 9001 10001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6001 = (segment_000000_pm_final pmStore) 6001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] } :: (segment_000000_pm_nodes.drop 6)) 6001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7001 = (segment_000000_pm_final pmStore) 7001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] } :: (segment_000000_pm_nodes.drop 6)) 7001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8001 = (segment_000000_pm_final pmStore) 8001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] } :: (segment_000000_pm_nodes.drop 6)) 8001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 9001 = (bw_matmul ((segment_000000_pm_final pmStore) 6001) ((segment_000000_pm_final pmStore) 7001) ((segment_000000_pm_final pmStore) 8001)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6001) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7001) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8001)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 6001) ((segment_000000_pm_final pmStore) 7001) ((segment_000000_pm_final pmStore) 8001)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_hPm0_2(pmStore:Store):(segment_000000_pm_final pmStore) 9002=(bw_matmul ((segment_000000_pm_final pmStore) 6002) ((segment_000000_pm_final pmStore) 7002) ((segment_000000_pm_final pmStore) 8002)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 6) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] }] ++ (segment_000000_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 9002 = (bw_matmul (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6002) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7002) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8002)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) (segment_000000_pm_nodes.drop 7)
      { rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] } 9002
      (fun t => (bw_matmul (t 6002) (t 7002) (t 8002)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out SyntheticRowHead.pmGraph t 2 6002 7002 8002 9002 10002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6002 = (segment_000000_pm_final pmStore) 6002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] } :: (segment_000000_pm_nodes.drop 7)) 6002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7002 = (segment_000000_pm_final pmStore) 7002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] } :: (segment_000000_pm_nodes.drop 7)) 7002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8002 = (segment_000000_pm_final pmStore) 8002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] } :: (segment_000000_pm_nodes.drop 7)) 8002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 9002 = (bw_matmul ((segment_000000_pm_final pmStore) 6002) ((segment_000000_pm_final pmStore) 7002) ((segment_000000_pm_final pmStore) 8002)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6002) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7002) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8002)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 6002) ((segment_000000_pm_final pmStore) 7002) ((segment_000000_pm_final pmStore) 8002)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_hPm0_3(pmStore:Store):(segment_000000_pm_final pmStore) 9003=(bw_matmul ((segment_000000_pm_final pmStore) 6003) ((segment_000000_pm_final pmStore) 7003) ((segment_000000_pm_final pmStore) 8003)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 9003 = (bw_matmul (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8003)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] } 9003
      (fun t => (bw_matmul (t 6003) (t 7003) (t 8003)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out SyntheticRowHead.pmGraph t 3 6003 7003 8003 9003 10003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6003 = (segment_000000_pm_final pmStore) 6003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] } :: (segment_000000_pm_nodes.drop 8)) 6003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7003 = (segment_000000_pm_final pmStore) 7003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] } :: (segment_000000_pm_nodes.drop 8)) 7003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8003 = (segment_000000_pm_final pmStore) 8003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] } :: (segment_000000_pm_nodes.drop 8)) 8003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 9003 = (bw_matmul ((segment_000000_pm_final pmStore) 6003) ((segment_000000_pm_final pmStore) 7003) ((segment_000000_pm_final pmStore) 8003)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8003)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 6003) ((segment_000000_pm_final pmStore) 7003) ((segment_000000_pm_final pmStore) 8003)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_hSm1(smStore:Store):(segment_000000_sm_final smStore) 901=(bw_matmul ((segment_000000_sm_final smStore) 600) ((segment_000000_sm_final smStore) 700) ((segment_000000_sm_final smStore) 800)).2:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 901 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 600) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 700) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 800)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] } 901
      (fun t => (bw_matmul (t 600) (t 700) (t 800)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out SyntheticRowHead.smGraph t 0 600 700 800 900 901 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 600 = (segment_000000_sm_final smStore) 600 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] } :: (segment_000000_sm_nodes.drop 1)) 600
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 700 = (segment_000000_sm_final smStore) 700 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] } :: (segment_000000_sm_nodes.drop 1)) 700
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 800 = (segment_000000_sm_final smStore) 800 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [600, 700, 800], outs := [900, 901] } :: (segment_000000_sm_nodes.drop 1)) 800
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 901 = (bw_matmul ((segment_000000_sm_final smStore) 600) ((segment_000000_sm_final smStore) 700) ((segment_000000_sm_final smStore) 800)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 600) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 700) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticRowHead.smGraph) smStore 800)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 600) ((segment_000000_sm_final smStore) 700) ((segment_000000_sm_final smStore) 800)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_hPm1_0(pmStore:Store):(segment_000000_pm_final pmStore) 10000=(bw_matmul ((segment_000000_pm_final pmStore) 6000) ((segment_000000_pm_final pmStore) 7000) ((segment_000000_pm_final pmStore) 8000)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 10000 = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] } 10000
      (fun t => (bw_matmul (t 6000) (t 7000) (t 8000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out SyntheticRowHead.pmGraph t 0 6000 7000 8000 9000 10000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6000 = (segment_000000_pm_final pmStore) 6000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] } :: (segment_000000_pm_nodes.drop 5)) 6000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7000 = (segment_000000_pm_final pmStore) 7000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] } :: (segment_000000_pm_nodes.drop 5)) 7000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8000 = (segment_000000_pm_final pmStore) 8000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [6000, 7000, 8000], outs := [9000, 10000] } :: (segment_000000_pm_nodes.drop 5)) 8000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 10000 = (bw_matmul ((segment_000000_pm_final pmStore) 6000) ((segment_000000_pm_final pmStore) 7000) ((segment_000000_pm_final pmStore) 8000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 6000) ((segment_000000_pm_final pmStore) 7000) ((segment_000000_pm_final pmStore) 8000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_hPm1_1(pmStore:Store):(segment_000000_pm_final pmStore) 10001=(bw_matmul ((segment_000000_pm_final pmStore) 6001) ((segment_000000_pm_final pmStore) 7001) ((segment_000000_pm_final pmStore) 8001)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 10001 = (bw_matmul (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6001) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7001) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8001)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] } 10001
      (fun t => (bw_matmul (t 6001) (t 7001) (t 8001)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out SyntheticRowHead.pmGraph t 1 6001 7001 8001 9001 10001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6001 = (segment_000000_pm_final pmStore) 6001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] } :: (segment_000000_pm_nodes.drop 6)) 6001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7001 = (segment_000000_pm_final pmStore) 7001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] } :: (segment_000000_pm_nodes.drop 6)) 7001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8001 = (segment_000000_pm_final pmStore) 8001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [6001, 7001, 8001], outs := [9001, 10001] } :: (segment_000000_pm_nodes.drop 6)) 8001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 10001 = (bw_matmul ((segment_000000_pm_final pmStore) 6001) ((segment_000000_pm_final pmStore) 7001) ((segment_000000_pm_final pmStore) 8001)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6001) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7001) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8001)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 6001) ((segment_000000_pm_final pmStore) 7001) ((segment_000000_pm_final pmStore) 8001)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_hPm1_2(pmStore:Store):(segment_000000_pm_final pmStore) 10002=(bw_matmul ((segment_000000_pm_final pmStore) 6002) ((segment_000000_pm_final pmStore) 7002) ((segment_000000_pm_final pmStore) 8002)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 6) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] }] ++ (segment_000000_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 10002 = (bw_matmul (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6002) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7002) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8002)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) (segment_000000_pm_nodes.drop 7)
      { rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] } 10002
      (fun t => (bw_matmul (t 6002) (t 7002) (t 8002)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out SyntheticRowHead.pmGraph t 2 6002 7002 8002 9002 10002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6002 = (segment_000000_pm_final pmStore) 6002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] } :: (segment_000000_pm_nodes.drop 7)) 6002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7002 = (segment_000000_pm_final pmStore) 7002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] } :: (segment_000000_pm_nodes.drop 7)) 7002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8002 = (segment_000000_pm_final pmStore) 8002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [6002, 7002, 8002], outs := [9002, 10002] } :: (segment_000000_pm_nodes.drop 7)) 8002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 10002 = (bw_matmul ((segment_000000_pm_final pmStore) 6002) ((segment_000000_pm_final pmStore) 7002) ((segment_000000_pm_final pmStore) 8002)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6002) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7002) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8002)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 6002) ((segment_000000_pm_final pmStore) 7002) ((segment_000000_pm_final pmStore) 8002)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_hPm1_3(pmStore:Store):(segment_000000_pm_final pmStore) 10003=(bw_matmul ((segment_000000_pm_final pmStore) 6003) ((segment_000000_pm_final pmStore) 7003) ((segment_000000_pm_final pmStore) 8003)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 10003 = (bw_matmul (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8003)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] } 10003
      (fun t => (bw_matmul (t 6003) (t 7003) (t 8003)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out SyntheticRowHead.pmGraph t 3 6003 7003 8003 9003 10003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6003 = (segment_000000_pm_final pmStore) 6003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] } :: (segment_000000_pm_nodes.drop 8)) 6003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7003 = (segment_000000_pm_final pmStore) 7003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] } :: (segment_000000_pm_nodes.drop 8)) 7003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8003 = (segment_000000_pm_final pmStore) 8003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticRowHead.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [6003, 7003, 8003], outs := [9003, 10003] } :: (segment_000000_pm_nodes.drop 8)) 8003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 10003 = (bw_matmul ((segment_000000_pm_final pmStore) 6003) ((segment_000000_pm_final pmStore) 7003) ((segment_000000_pm_final pmStore) 8003)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 6003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 7003) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticRowHead.pmGraph) pmStore 8003)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 6003) ((segment_000000_pm_final pmStore) 7003) ((segment_000000_pm_final pmStore) 8003)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_head_transpose_shape (t:Tensor)(a b c d:Nat)(ht:t.shape=[a,b,c,d]):(transpose2d t).shape=[a,b,d,c]:=by
  simp only [transpose2d,ht,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,Tensor.mkShape]
set_option maxHeartbeats 500000 in
private theorem segment_000000_head_sound(smStore pmStore:Store)(hstate:state_before.Holds smStore pmStore):segment_000000_head_post.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore):=by
  let smFinal:=segment_000000_sm_final smStore
  let pmFinal:=segment_000000_pm_final pmStore
  have hframe:state_before.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final;apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg:mg.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 600) [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003] 1 [2, 8, 3, 7] [2, 2, 3, 7] at hg
  have hgV:smFinal 600=allGatherPrimDimN 1 4 0 [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003]:=by simpa only [List.length_cons,List.length_nil] using hg.full_value
  have hx:mx.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 700) [pmFinal 7000, pmFinal 7001, pmFinal 7002, pmFinal 7003] 1 [2, 8, 3, 5] [2, 2, 3, 5] at hx
  have hxV:smFinal 700=allGatherPrimDimN 1 4 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002, pmFinal 7003]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
  have hy:my.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 800) [pmFinal 8000, pmFinal 8001, pmFinal 8002, pmFinal 8003] 1 [2, 8, 5, 7] [2, 2, 5, 7] at hy
  have hyV:smFinal 800=allGatherPrimDimN 1 4 0 [pmFinal 8000, pmFinal 8001, pmFinal 8002, pmFinal 8003]:=by simpa only [List.length_cons,List.length_nil] using hy.full_value
  have hS0:smFinal 900=(bw_matmul (smFinal 600) (smFinal 700) (smFinal 800)).1:=segment_000000_head_hSm0 smStore
  have hP0_0:pmFinal 9000=(bw_matmul (pmFinal 6000) (pmFinal 7000) (pmFinal 8000)).1:=segment_000000_head_hPm0_0 pmStore
  have hP0_1:pmFinal 9001=(bw_matmul (pmFinal 6001) (pmFinal 7001) (pmFinal 8001)).1:=segment_000000_head_hPm0_1 pmStore
  have hP0_2:pmFinal 9002=(bw_matmul (pmFinal 6002) (pmFinal 7002) (pmFinal 8002)).1:=segment_000000_head_hPm0_2 pmStore
  have hP0_3:pmFinal 9003=(bw_matmul (pmFinal 6003) (pmFinal 7003) (pmFinal 8003)).1:=segment_000000_head_hPm0_3 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP0_0
  simp only [bw_matmul,batchedMatmulBwd] at hP0_1
  simp only [bw_matmul,batchedMatmulBwd] at hP0_2
  simp only [bw_matmul,batchedMatmulBwd] at hP0_3
  have hC0:=TrainVerify.Denote.bw_matmul_fst_head_gather_rank4 4 2 2 3 5 7 [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003] [pmFinal 7000, pmFinal 7001, pmFinal 7002, pmFinal 7003] [pmFinal 8000, pmFinal 8001, pmFinal 8002, pmFinal 8003]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV0:smFinal 900=allGatherPrimDimN 1 4 0 [pmFinal 9000, pmFinal 9001, pmFinal 9002, pmFinal 9003]:=by
    rw [hS0,hgV,hxV,hyV,hC0]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP0_0, ←hP0_1, ←hP0_2, ←hP0_3]
  have hFull0:(smFinal 900).shape=[2, 8, 3, 5]:=by rw [hS0];exact fw_matmul_rank4_shape _ _ 2 8 3 7 5 hg.full_shape (segment_000000_head_transpose_shape _ 2 8 5 7 hy.full_shape)
  have hout0:mo0.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 900) [pmFinal 9000, pmFinal 9001, pmFinal 9002, pmFinal 9003] 1 [2, 8, 3, 5] [2, 2, 3, 5]
    refine {full_value:=hV0,full_shape:=hFull0,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1 | hh2 | hh3
      · subst piece;rw [hP0_0];exact fw_matmul_rank4_shape _ _ 2 2 3 7 5 (hg.shard_shapes (pmFinal 6000) (by simp)) (segment_000000_head_transpose_shape _ 2 2 5 7 (hy.shard_shapes (pmFinal 8000) (by simp)))
      · subst piece;rw [hP0_1];exact fw_matmul_rank4_shape _ _ 2 2 3 7 5 (hg.shard_shapes (pmFinal 6001) (by simp)) (segment_000000_head_transpose_shape _ 2 2 5 7 (hy.shard_shapes (pmFinal 8001) (by simp)))
      · subst piece;rw [hP0_2];exact fw_matmul_rank4_shape _ _ 2 2 3 7 5 (hg.shard_shapes (pmFinal 6002) (by simp)) (segment_000000_head_transpose_shape _ 2 2 5 7 (hy.shard_shapes (pmFinal 8002) (by simp)))
      · subst piece;rw [hP0_3];exact fw_matmul_rank4_shape _ _ 2 2 3 7 5 (hg.shard_shapes (pmFinal 6003) (by simp)) (segment_000000_head_transpose_shape _ 2 2 5 7 (hy.shard_shapes (pmFinal 8003) (by simp)))
    · simp only [List.length_cons,List.length_nil];native_decide
  have hS1:smFinal 901=(bw_matmul (smFinal 600) (smFinal 700) (smFinal 800)).2:=segment_000000_head_hSm1 smStore
  have hP1_0:pmFinal 10000=(bw_matmul (pmFinal 6000) (pmFinal 7000) (pmFinal 8000)).2:=segment_000000_head_hPm1_0 pmStore
  have hP1_1:pmFinal 10001=(bw_matmul (pmFinal 6001) (pmFinal 7001) (pmFinal 8001)).2:=segment_000000_head_hPm1_1 pmStore
  have hP1_2:pmFinal 10002=(bw_matmul (pmFinal 6002) (pmFinal 7002) (pmFinal 8002)).2:=segment_000000_head_hPm1_2 pmStore
  have hP1_3:pmFinal 10003=(bw_matmul (pmFinal 6003) (pmFinal 7003) (pmFinal 8003)).2:=segment_000000_head_hPm1_3 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP1_0
  simp only [bw_matmul,batchedMatmulBwd] at hP1_1
  simp only [bw_matmul,batchedMatmulBwd] at hP1_2
  simp only [bw_matmul,batchedMatmulBwd] at hP1_3
  have hC1:=TrainVerify.Denote.bw_matmul_snd_head_gather_rank4 4 2 2 3 5 7 [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003] [pmFinal 7000, pmFinal 7001, pmFinal 7002, pmFinal 7003] [pmFinal 8000, pmFinal 8001, pmFinal 8002, pmFinal 8003]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV1:smFinal 901=allGatherPrimDimN 1 4 0 [pmFinal 10000, pmFinal 10001, pmFinal 10002, pmFinal 10003]:=by
    rw [hS1,hgV,hxV,hyV,hC1]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP1_0, ←hP1_1, ←hP1_2, ←hP1_3]
  have hFull1:(smFinal 901).shape=[2, 8, 5, 7]:=by rw [hS1];exact fw_matmul_rank4_shape _ _ 2 8 5 3 7 (segment_000000_head_transpose_shape _ 2 8 3 5 hx.full_shape) hg.full_shape
  have hout1:mo1.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 901) [pmFinal 10000, pmFinal 10001, pmFinal 10002, pmFinal 10003] 1 [2, 8, 5, 7] [2, 2, 5, 7]
    refine {full_value:=hV1,full_shape:=hFull1,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1 | hh2 | hh3
      · subst piece;rw [hP1_0];exact fw_matmul_rank4_shape _ _ 2 2 5 3 7 (segment_000000_head_transpose_shape _ 2 2 3 5 (hx.shard_shapes (pmFinal 7000) (by simp))) (hg.shard_shapes (pmFinal 6000) (by simp))
      · subst piece;rw [hP1_1];exact fw_matmul_rank4_shape _ _ 2 2 5 3 7 (segment_000000_head_transpose_shape _ 2 2 3 5 (hx.shard_shapes (pmFinal 7001) (by simp))) (hg.shard_shapes (pmFinal 6001) (by simp))
      · subst piece;rw [hP1_2];exact fw_matmul_rank4_shape _ _ 2 2 5 3 7 (segment_000000_head_transpose_shape _ 2 2 3 5 (hx.shard_shapes (pmFinal 7002) (by simp))) (hg.shard_shapes (pmFinal 6002) (by simp))
      · subst piece;rw [hP1_3];exact fw_matmul_rank4_shape _ _ 2 2 5 3 7 (segment_000000_head_transpose_shape _ 2 2 3 5 (hx.shard_shapes (pmFinal 7003) (by simp))) (hg.shard_shapes (pmFinal 6003) (by simp))
    · simp only [List.length_cons,List.length_nil];native_decide
  intro fact hfact
  have hc:fact∈[mo0, mo1]++state_before.facts:=(show segment_000000_head_post.facts⊆[mo0, mo1]++state_before.facts by native_decide) hfact
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with (rfl | rfl) | old
  · exact hout0
  · exact hout1
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticRowHead.smGraph SyntheticRowHead.pmGraph state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h0 := segment_000000_row_sound smStore pmStore hstate
    have h1 := segment_000000_head_sound smStore pmStore hstate
    change state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore)
    intro fact hfact
    have hc : fact ∈ segment_000000_row_post.facts ∨ fact ∈ segment_000000_head_post.facts := by
      have hsub : state_after.facts ⊆ segment_000000_row_post.facts ++ segment_000000_head_post.facts := by native_decide
      exact List.mem_append.mp (hsub hfact)
    rcases hc with h | h
    · exact h0 fact h
    · exact h1 fact h

#print axioms segment_000000
end
end SyntheticRowHead
