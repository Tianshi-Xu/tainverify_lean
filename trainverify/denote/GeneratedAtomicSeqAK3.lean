import denote.RelationCompiler
import denote.KRankBWLinearDwSequenceGeneral
import denote.KRankBWLinearDxSequence
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SequenceLinearAllToAll
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 2] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 15, 7] [2, 5, 7]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002] 1 [2, 15, 11] [2, 5, 11]
def fact_w : RelationFact := .sharded 206 [206] 0 [7, 11] [7, 11]
def fact_dw : RelationFact := .reduction 401 [5000, 5001, 5002] [7, 11]
def fact_out : RelationFact := .sharded 400 [4000, 4001, 4002] 1 [2, 15, 11] [2, 5, 11]
def fact_a_in : RelationFact := .sharded 700 [7000, 7001, 7002] 1 [2, 15, 33] [2, 5, 33]
def fact_a_out : RelationFact := .sharded 700 [8000, 8001, 8002] 2 [2, 15, 33] [2, 15, 11]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_a_in]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_dw, fact_out, fact_a_in, fact_a_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 2] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) s

set_option maxHeartbeats 500000 in
private theorem segment_000000_hSmWriter1 (store : Store) : (segment_000000_sm_final store) 401 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).2 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 401 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 206)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } 401
      (fun t => (bw_linear (t 100) (t 200) (t 206)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SequenceLinearAllToAll.smGraph t 0 100 200 206 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 206 = (segment_000000_sm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 401 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).2 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 206)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter1_0 (store : Store) : (segment_000000_pm_final store) 5000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 5000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } 5000
      (fun t => (bw_linear (t 1000) (t 2000) (t 206)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SequenceLinearAllToAll.pmGraph t 0 1000 2000 206 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 5000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter1_1 (store : Store) : (segment_000000_pm_final store) 5001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 5001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } 5001
      (fun t => (bw_linear (t 1001) (t 2001) (t 206)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SequenceLinearAllToAll.pmGraph t 1 1001 2001 206 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2001 = (segment_000000_pm_final store) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 5001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter1_2 (store : Store) : (segment_000000_pm_final store) 5002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 5002 = (bw_linear (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } 5002
      (fun t => (bw_linear (t 1002) (t 2002) (t 206)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SequenceLinearAllToAll.pmGraph t 2 1002 2002 206 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1002 = (segment_000000_pm_final store) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 6)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2002 = (segment_000000_pm_final store) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 6)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 6)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 5002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hSmWriter0 (store : Store) : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 400 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 206)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 206)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SequenceLinearAllToAll.smGraph t 0 100 200 206 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 206 = (segment_000000_sm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.smGraph) store 206)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter0_0 (store : Store) : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 206)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SequenceLinearAllToAll.pmGraph t 0 1000 2000 206 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter0_1 (store : Store) : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1001) (t 2001) (t 206)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SequenceLinearAllToAll.pmGraph t 1 1001 2001 206 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2001 = (segment_000000_pm_final store) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter0_2 (store : Store) : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4002 = (bw_linear (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } 4002
      (fun t => (bw_linear (t 1002) (t 2002) (t 206)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SequenceLinearAllToAll.pmGraph t 2 1002 2002 206 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1002 = (segment_000000_pm_final store) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 6)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2002 = (segment_000000_pm_final store) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 6)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 6)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 1002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 2002) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 206)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hAllToAll0 (store : Store) : (segment_000000_pm_final store) 8000 = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 0 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 8000 = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 0 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7000, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7001, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7002] 1 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 2] } 8000
      (fun t => allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 0 [t 7000, t 7001, t 7002] 1 2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out SequenceLinearAllToAll.pmGraph t 0 [7000, 7001, 7002] 8000 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7000 = (segment_000000_pm_final store) 7000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 2] } :: (segment_000000_pm_nodes.drop 3)) 7000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7001 = (segment_000000_pm_final store) 7001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 2] } :: (segment_000000_pm_nodes.drop 3)) 7001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7002 = (segment_000000_pm_final store) 7002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8000], params := [1, 2] } :: (segment_000000_pm_nodes.drop 3)) 7002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 8000 = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 0 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 2 := by
    calc
      _ = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 0 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7000, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7001, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7002] 1 2 := hout_prefix
      _ = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 0 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hAllToAll1 (store : Store) : (segment_000000_pm_final store) 8001 = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 1 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 8001 = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 1 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7000, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7001, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7002] 1 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 2] } 8001
      (fun t => allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 1 [t 7000, t 7001, t 7002] 1 2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out SequenceLinearAllToAll.pmGraph t 1 [7000, 7001, 7002] 8001 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7000 = (segment_000000_pm_final store) 7000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 2] } :: (segment_000000_pm_nodes.drop 4)) 7000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7001 = (segment_000000_pm_final store) 7001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 2] } :: (segment_000000_pm_nodes.drop 4)) 7001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7002 = (segment_000000_pm_final store) 7002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8001], params := [1, 2] } :: (segment_000000_pm_nodes.drop 4)) 7002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 8001 = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 1 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 2 := by
    calc
      _ = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 1 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7000, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7001, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7002] 1 2 := hout_prefix
      _ = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 1 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hAllToAll2 (store : Store) : (segment_000000_pm_final store) 8002 = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 2 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 2] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 8002 = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 2 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7000, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7001, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7002] 1 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 2] } 8002
      (fun t => allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 2 [t 7000, t 7001, t 7002] 1 2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out SequenceLinearAllToAll.pmGraph t 2 [7000, 7001, 7002] 8002 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7000 = (segment_000000_pm_final store) 7000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 2] } :: (segment_000000_pm_nodes.drop 5)) 7000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7001 = (segment_000000_pm_final store) 7001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 2] } :: (segment_000000_pm_nodes.drop 5)) 7001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7002 = (segment_000000_pm_final store) 7002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceLinearAllToAll.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [7000, 7001, 7002], outs := [8002], params := [1, 2] } :: (segment_000000_pm_nodes.drop 5)) 7002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 8002 = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 2 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 2 := by
    calc
      _ = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 2 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7000, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7001, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceLinearAllToAll.pmGraph) store 7002] 1 2 := hout_prefix
      _ = allToAllPrimWithDims SequenceLinearAllToAll.pmGraph.numRanks 2 [(segment_000000_pm_final store) 7000, (segment_000000_pm_final store) 7001, (segment_000000_pm_final store) 7002] 1 2 := by rw [hout_read_0, hout_read_1, hout_read_2]
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
 change ShardedRel (smFinal 206) [pmFinal 206] 0 [7, 11] [7, 11] at hw
 have hwEq : smFinal 206 = pmFinal 206 := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)]; decide)
 have hgV : smFinal 100 = allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002] := by simpa only [List.length_cons,List.length_nil] using hg.full_value
 have hxV : smFinal 200 = allGatherPrimDimN 1 3 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002] := by simpa only [List.length_cons,List.length_nil] using hx.full_value
 have hS1 : smFinal 401 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 206)).2 := segment_000000_hSmWriter1 smStore
 have hP1_0 : pmFinal 5000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 206)).2 := segment_000000_hPmWriter1_0 pmStore
 have hP1_1 : pmFinal 5001 = (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 206)).2 := segment_000000_hPmWriter1_1 pmStore
 have hP1_2 : pmFinal 5002 = (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 206)).2 := segment_000000_hPmWriter1_2 pmStore
 have hcomm1 := TrainVerify.Denote.bw_linear_dw_sequence_reduction_rank3 3 2 5 7 11 [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] (pmFinal 206)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes (hw.shard_shapes _ (by simp))
 simp only [List.zipWith] at hcomm1
 have hV1 : smFinal 401 = tensorSum [pmFinal 5000, pmFinal 5001, pmFinal 5002] := by
   rw [hS1, hgV, hxV, hwEq, hcomm1]
   rw [← hP1_0, ← hP1_1, ← hP1_2]
 have hFull1 : (smFinal 401).shape = [7, 11] := by rw [hS1]; exact bw_linear_3d_snd_shape 2 15 7 11 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape1_0 : (pmFinal 5000).shape = [7, 11] := by rw [hP1_0]; exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1_1 : (pmFinal 5001).shape = [7, 11] := by rw [hP1_1]; exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1_2 : (pmFinal 5002).shape = [7, 11] := by rw [hP1_2]; exact bw_linear_3d_snd_shape 2 5 7 11 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout1 : fact_dw.Holds smFinal pmFinal := by
   change ReductionRel (smFinal 401) [pmFinal 5000, pmFinal 5001, pmFinal 5002] [7, 11]
   have hReduce : smFinal 401 = allReducePrim [pmFinal 5000, pmFinal 5001, pmFinal 5002].length 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002] := by rw [hV1]; rfl
   refine { full_value := hReduce, full_shape := hFull1, contributions_nonempty := by simp, contribution_shapes := ?_, reduced_shape := ?_ }
   · simp only [List.forall_mem_cons]; exact ⟨hShape1_0, hShape1_1, hShape1_2, List.forall_mem_nil _⟩
   · rw [← hReduce]; exact hFull1
 have hS0 : smFinal 400 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 206)).1 := segment_000000_hSmWriter0 smStore
 have hP0_0 : pmFinal 4000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 206)).1 := segment_000000_hPmWriter0_0 pmStore
 have hP0_1 : pmFinal 4001 = (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 206)).1 := segment_000000_hPmWriter0_1 pmStore
 have hP0_2 : pmFinal 4002 = (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 206)).1 := segment_000000_hPmWriter0_2 pmStore
 have hcomm0 := TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 3 2 5 7 11 [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] (smFinal 200) (pmFinal 206)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes hx.full_shape (hw.shard_shapes _ (by simp))
 simp only [List.zipWith] at hcomm0
 have hV0 : smFinal 400 = allGatherPrimDimN 1 3 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002] := by
   rw [hS0, hgV, hwEq, hcomm0]
   rw [← hP0_0, ← hP0_1, ← hP0_2]
 have hFull0 : (smFinal 400).shape = [2, 15, 11] := by rw [hS0]; exact bw_linear_3d_fst_shape 2 15 7 11 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape0_0 : (pmFinal 4000).shape = [2, 5, 11] := by rw [hP0_0]; exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape0_1 : (pmFinal 4001).shape = [2, 5, 11] := by rw [hP0_1]; exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape0_2 : (pmFinal 4002).shape = [2, 5, 11] := by rw [hP0_2]; exact bw_linear_3d_fst_shape 2 5 7 11 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout0 : fact_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002] 1 [2, 15, 11] [2, 5, 11]
   refine { full_value := ?_, full_shape := hFull0, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simpa only [List.length_cons,List.length_nil] using hV0
   · simp only [List.forall_mem_cons]; exact ⟨hShape0_0, hShape0_1, hShape0_2, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 have hai : fact_a_in.Holds smFinal pmFinal := hframe _ (by native_decide)
 change ShardedRel (smFinal 700) [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 [2, 15, 33] [2, 5, 33] at hai
 have hA0 : pmFinal 8000 = allToAllPrimWithDims 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 2 := segment_000000_hAllToAll0 pmStore
 have hA1 : pmFinal 8001 = allToAllPrimWithDims 3 1 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 2 := segment_000000_hAllToAll1 pmStore
 have hA2 : pmFinal 8002 = allToAllPrimWithDims 3 2 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 2 := segment_000000_hAllToAll2 pmStore
 have hHead : (([pmFinal 7000, pmFinal 7001, pmFinal 7002].head?.map (fun t => t.shape)).getD []) = [2, 5, 33] := hai.shard_shapes _ (by simp)
 have hAV : smFinal 700 = allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002] := by simpa only [List.length_cons,List.length_nil] using hai.full_value
 have hGS : (allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002]).shape = [2, 15, 33] := by rw [←hAV]; exact hai.full_shape
 have hOd : 2 < (allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002]).shape.length := by rw [hGS]; decide
 have hDv : (allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002]).shape.getD 2 0 % 3 = 0 := by rw [hGS]; decide
 have hAS0 : (pmFinal 8000).shape = [2, 15, 11] := by rw [hA0,allToAllPrimWithDims_shape 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 2 [2, 5, 33] hHead (by decide)]; decide
 have hAS1 : (pmFinal 8001).shape = [2, 15, 11] := by rw [hA1,allToAllPrimWithDims_shape 3 1 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 2 [2, 5, 33] hHead (by decide)]; decide
 have hAS2 : (pmFinal 8002).shape = [2, 15, 11] := by rw [hA2,allToAllPrimWithDims_shape 3 2 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 2 [2, 5, 33] hHead (by decide)]; decide
 have hOrd : [pmFinal 8000, pmFinal 8001, pmFinal 8002] = List.ofFn (fun r : Fin 3 => allToAllPrimWithDims 3 r.1 [pmFinal 7000, pmFinal 7001, pmFinal 7002] 1 2) := by rw [hA0, hA1, hA2]; rfl
 have hAC : allGatherPrimDimN 2 [pmFinal 8000, pmFinal 8001, pmFinal 8002].length 0 [pmFinal 8000, pmFinal 8001, pmFinal 8002] = allGatherPrimDimN 1 3 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002] := by rw [hOrd]; simpa only [List.length_cons,List.length_nil,List.length_ofFn] using (TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 2 [pmFinal 7000, pmFinal 7001, pmFinal 7002] (by simp) hOd hDv)
 have houtA : fact_a_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 700) [pmFinal 8000, pmFinal 8001, pmFinal 8002] 2 [2, 15, 33] [2, 15, 11]
   refine { full_value := ?_, full_shape := hai.full_shape, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · rw [hAC]; exact hAV
   · simp only [List.forall_mem_cons]; exact ⟨hAS0, hAS1, hAS2, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 intro fact hfact
 have hc : fact ∈ [fact_dw, fact_out, fact_a_out] ++ state_before.facts := (show state_after.facts ⊆ [fact_dw, fact_out, fact_a_out] ++ state_before.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh | old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
   rcases fresh with rfl | rfl | rfl
   · exact hout1
   · exact hout0
   · exact houtA
 · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SequenceLinearAllToAll.smGraph SequenceLinearAllToAll.pmGraph state_before state_after where
 smNodes := segment_000000_sm_nodes
 pmNodes := segment_000000_pm_nodes
 sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000
end
end SequenceLinearAllToAll
