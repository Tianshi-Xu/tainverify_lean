import denote.RelationCompiler
import denote.KRankBWLinearDwSequenceGeneral
import denote.KRankBWLinearDxSequence
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SequenceDwCase3_1
set_option maxHeartbeats 500000
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] }, { rank := 0, op := "OpName.FW_neg", ins := [9010], outs := [9011] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] }, { rank := 0, op := "OpName.FW_neg", ins := [9000], outs := [9001] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 1 [1, 16, 64] [1, 4, 64]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 1 [1, 16, 64] [1, 4, 64]
def fact_w : RelationFact := .sharded 206 [206] 0 [64, 64] [64, 64]
def fact_dw : RelationFact := .reduction 401 [5000, 5001, 5002, 5003] [64, 64]
def fact_out : RelationFact := .sharded 400 [4000, 4001, 4002, 4003] 1 [1, 16, 64] [1, 4, 64]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_dw, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] }, { rank := 0, op := "OpName.FW_neg", ins := [9010], outs := [9011] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] }, { rank := 0, op := "OpName.FW_neg", ins := [9000], outs := [9001] }, { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) s

set_option maxHeartbeats 500000 in
private theorem segment_000000_hSmWriter1 (store : Store) : (segment_000000_sm_final store) 401 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).2 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 401 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 206)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } 401
      (fun t => (bw_linear (t 100) (t 200) (t 206)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SequenceDwCase3_1.smGraph t 0 100 200 206 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 206 = (segment_000000_sm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 401 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).2 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 206)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter1_0 (store : Store) : (segment_000000_pm_final store) 5000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 5000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } 5000
      (fun t => (bw_linear (t 1000) (t 2000) (t 206)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SequenceDwCase3_1.pmGraph t 0 1000 2000 206 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 5000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter1_1 (store : Store) : (segment_000000_pm_final store) 5001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 5001 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } 5001
      (fun t => (bw_linear (t 1001) (t 2001) (t 206)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SequenceDwCase3_1.pmGraph t 1 1001 2001 206 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 3)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2001 = (segment_000000_pm_final store) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 3)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 3)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 5001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter1_2 (store : Store) : (segment_000000_pm_final store) 5002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 5002 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } 5002
      (fun t => (bw_linear (t 1002) (t 2002) (t 206)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SequenceDwCase3_1.pmGraph t 2 1002 2002 206 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1002 = (segment_000000_pm_final store) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 4)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2002 = (segment_000000_pm_final store) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 4)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 4)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 5002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter1_3 (store : Store) : (segment_000000_pm_final store) 5003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 206)).2 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 5003 = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] } 5003
      (fun t => (bw_linear (t 1003) (t 2003) (t 206)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out SequenceDwCase3_1.pmGraph t 3 1003 2003 206 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1003 = (segment_000000_pm_final store) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 5)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2003 = (segment_000000_pm_final store) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 5)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 5)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 5003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 206)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 206)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hSmWriter0 (store : Store) : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final store) 400 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 206)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.smGraph store
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 206)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SequenceDwCase3_1.smGraph t 0 100 200 206 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 100 = (segment_000000_sm_final store) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 200 = (segment_000000_sm_final store) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 206 = (segment_000000_sm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.smGraph store
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 206], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final store) 400 = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.smGraph) store 206)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final store) 100) ((segment_000000_sm_final store) 200) ((segment_000000_sm_final store) 206)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter0_0 (store : Store) : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 206)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SequenceDwCase3_1.pmGraph t 0 1000 2000 206 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1000 = (segment_000000_pm_final store) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2000 = (segment_000000_pm_final store) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 206], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4000 = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1000) ((segment_000000_pm_final store) 2000) ((segment_000000_pm_final store) 206)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter0_1 (store : Store) : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4001 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1001) (t 2001) (t 206)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SequenceDwCase3_1.pmGraph t 1 1001 2001 206 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1001 = (segment_000000_pm_final store) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 3)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2001 = (segment_000000_pm_final store) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 3)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_linear", ins := [1001, 2001, 206], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 3)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4001 = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1001) ((segment_000000_pm_final store) 2001) ((segment_000000_pm_final store) 206)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter0_2 (store : Store) : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4002 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } 4002
      (fun t => (bw_linear (t 1002) (t 2002) (t 206)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SequenceDwCase3_1.pmGraph t 2 1002 2002 206 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1002 = (segment_000000_pm_final store) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 4)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2002 = (segment_000000_pm_final store) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 4)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 3) ({ rank := 2, op := "OpName.BW_linear", ins := [1002, 2002, 206], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 4)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4002 = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1002) ((segment_000000_pm_final store) 2002) ((segment_000000_pm_final store) 206)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_hPmWriter0_3 (store : Store) : (segment_000000_pm_final store) 4003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 206)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 4003 = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] } 4003
      (fun t => (bw_linear (t 1003) (t 2003) (t 206)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SequenceDwCase3_1.pmGraph t 3 1003 2003 206 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1003 = (segment_000000_pm_final store) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 5)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2003 = (segment_000000_pm_final store) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 5)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206 = (segment_000000_pm_final store) 206 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SequenceDwCase3_1.pmGraph store
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_linear", ins := [1003, 2003, 206], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 5)) 206
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 4003 = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 206)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 1003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 2003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SequenceDwCase3_1.pmGraph) store 206)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final store) 1003) ((segment_000000_pm_final store) 2003) ((segment_000000_pm_final store) 206)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
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
 change ShardedRel (smFinal 206) [pmFinal 206] 0 [64, 64] [64, 64] at hw
 have hwEq : smFinal 206 = pmFinal 206 := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)]; decide)
 have hgV : smFinal 100 = allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] := by simpa only [List.length_cons,List.length_nil] using hg.full_value
 have hxV : smFinal 200 = allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] := by simpa only [List.length_cons,List.length_nil] using hx.full_value
 have hS1 : smFinal 401 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 206)).2 := segment_000000_hSmWriter1 smStore
 have hP1_0 : pmFinal 5000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 206)).2 := segment_000000_hPmWriter1_0 pmStore
 have hP1_1 : pmFinal 5001 = (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 206)).2 := segment_000000_hPmWriter1_1 pmStore
 have hP1_2 : pmFinal 5002 = (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 206)).2 := segment_000000_hPmWriter1_2 pmStore
 have hP1_3 : pmFinal 5003 = (bw_linear (pmFinal 1003) (pmFinal 2003) (pmFinal 206)).2 := segment_000000_hPmWriter1_3 pmStore
 have hcomm1 := TrainVerify.Denote.bw_linear_dw_sequence_reduction_rank3 4 1 4 64 64 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] (pmFinal 206)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes (hw.shard_shapes _ (by simp))
 simp only [List.zipWith] at hcomm1
 have hV1 : smFinal 401 = tensorSum [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] := by
   rw [hS1, hgV, hxV, hwEq, hcomm1]
   rw [← hP1_0, ← hP1_1, ← hP1_2, ← hP1_3]
 have hFull1 : (smFinal 401).shape = [64, 64] := by rw [hS1]; exact bw_linear_3d_snd_shape 1 16 64 64 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape1_0 : (pmFinal 5000).shape = [64, 64] := by rw [hP1_0]; exact bw_linear_3d_snd_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1_1 : (pmFinal 5001).shape = [64, 64] := by rw [hP1_1]; exact bw_linear_3d_snd_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1_2 : (pmFinal 5002).shape = [64, 64] := by rw [hP1_2]; exact bw_linear_3d_snd_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape1_3 : (pmFinal 5003).shape = [64, 64] := by rw [hP1_3]; exact bw_linear_3d_snd_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout1 : fact_dw.Holds smFinal pmFinal := by
   change ReductionRel (smFinal 401) [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] [64, 64]
   have hReduce : smFinal 401 = allReducePrim [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003].length 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] := by rw [hV1]; rfl
   refine { full_value := hReduce, full_shape := hFull1, contributions_nonempty := by simp, contribution_shapes := ?_, reduced_shape := ?_ }
   · simp only [List.forall_mem_cons]; exact ⟨hShape1_0, hShape1_1, hShape1_2, hShape1_3, List.forall_mem_nil _⟩
   · rw [← hReduce]; exact hFull1
 have hS0 : smFinal 400 = (bw_linear (smFinal 100) (smFinal 200) (smFinal 206)).1 := segment_000000_hSmWriter0 smStore
 have hP0_0 : pmFinal 4000 = (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 206)).1 := segment_000000_hPmWriter0_0 pmStore
 have hP0_1 : pmFinal 4001 = (bw_linear (pmFinal 1001) (pmFinal 2001) (pmFinal 206)).1 := segment_000000_hPmWriter0_1 pmStore
 have hP0_2 : pmFinal 4002 = (bw_linear (pmFinal 1002) (pmFinal 2002) (pmFinal 206)).1 := segment_000000_hPmWriter0_2 pmStore
 have hP0_3 : pmFinal 4003 = (bw_linear (pmFinal 1003) (pmFinal 2003) (pmFinal 206)).1 := segment_000000_hPmWriter0_3 pmStore
 have hcomm0 := TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 4 1 4 64 64 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] (smFinal 200) (pmFinal 206)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes hx.full_shape (hw.shard_shapes _ (by simp))
 simp only [List.zipWith] at hcomm0
 have hV0 : smFinal 400 = allGatherPrimDimN 1 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] := by
   rw [hS0, hgV, hwEq, hcomm0]
   rw [← hP0_0, ← hP0_1, ← hP0_2, ← hP0_3]
 have hFull0 : (smFinal 400).shape = [1, 16, 64] := by rw [hS0]; exact bw_linear_3d_fst_shape 1 16 64 64 _ _ _ hg.full_shape hx.full_shape hw.full_shape
 have hShape0_0 : (pmFinal 4000).shape = [1, 4, 64] := by rw [hP0_0]; exact bw_linear_3d_fst_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape0_1 : (pmFinal 4001).shape = [1, 4, 64] := by rw [hP0_1]; exact bw_linear_3d_fst_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape0_2 : (pmFinal 4002).shape = [1, 4, 64] := by rw [hP0_2]; exact bw_linear_3d_fst_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hShape0_3 : (pmFinal 4003).shape = [1, 4, 64] := by rw [hP0_3]; exact bw_linear_3d_fst_shape 1 4 64 64 _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hout0 : fact_out.Holds smFinal pmFinal := by
   change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 1 [1, 16, 64] [1, 4, 64]
   refine { full_value := ?_, full_shape := hFull0, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
   · simpa only [List.length_cons,List.length_nil] using hV0
   · simp only [List.forall_mem_cons]; exact ⟨hShape0_0, hShape0_1, hShape0_2, hShape0_3, List.forall_mem_nil _⟩
   · simp only [List.length_cons,List.length_nil]; decide
 intro fact hfact
 have hc : fact ∈ [fact_dw, fact_out] ++ state_before.facts := (show state_after.facts ⊆ [fact_dw, fact_out] ++ state_before.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh | old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
   rcases fresh with rfl | rfl
   · exact hout1
   · exact hout0
 · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SequenceDwCase3_1.smGraph SequenceDwCase3_1.pmGraph state_before state_after where
 smNodes := segment_000000_sm_nodes
 pmNodes := segment_000000_pm_nodes
 sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000
end
end SequenceDwCase3_1
