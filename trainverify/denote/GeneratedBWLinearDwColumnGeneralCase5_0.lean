import denote.RelationCompiler
import denote.KRankBWLinearDwColumnGeneral
import denote.KRankBWLinearDxColumnGeneral
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ColumnDwCase5_0
set_option maxHeartbeats 500000
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }, { rank := 0, op := "OpName.FW_neg", ins := [9010], outs := [9011] }, { rank := 0, op := "OpName.BW_view", ins := [100, 100], outs := [110], params := [1, 16, 64] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 0, op := "OpName.FW_neg", ins := [9000], outs := [9001] }, { rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] }, { rank := 0, op := "OpName.BW_view", ins := [1000, 1000], outs := [1100], params := [1, 16, 64] }] }
def fact_g : RelationFact := .joined 100 1000 [1, 16, 64]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 2 [1, 16, 64] [1, 16, 16]
def fact_w : RelationFact := .sharded 300 [3000, 3001, 3002, 3003] 1 [64, 64] [64, 16]
def fact_dw : RelationFact := .sharded 401 [5000, 5001, 5002, 5003] 1 [64, 64] [64, 16]
def fact_view : RelationFact := .joined 110 1100 [1, 16, 64]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_dw, fact_view]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }, { rank := 0, op := "OpName.FW_neg", ins := [9010], outs := [9011] }, { rank := 0, op := "OpName.BW_view", ins := [100, 100], outs := [110], params := [1, 16, 64] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 0, op := "OpName.FW_neg", ins := [9000], outs := [9001] }, { rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] }, { rank := 0, op := "OpName.BW_view", ins := [1000, 1000], outs := [1100], params := [1, 16, 64] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 401 = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ColumnDwCase5_0.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_linear (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out ColumnDwCase5_0.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5000 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_linear (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out ColumnDwCase5_0.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5001 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3001)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] } 5001
      (fun t => (bw_linear (t 1000) (t 2001) (t 3001)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out ColumnDwCase5_0.pmGraph t 1 1000 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 3)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 3)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 3)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3001)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5002 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3002)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] } 5002
      (fun t => (bw_linear (t 1000) (t 2002) (t 3002)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out ColumnDwCase5_0.pmGraph t 2 1000 2002 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 4)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 4)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 4)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3002)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 5003 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5003 = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3003)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] } 5003
      (fun t => (bw_linear (t 1000) (t 2003) (t 3003)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out ColumnDwCase5_0.pmGraph t 3 1000 2003 3003 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 5)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 5)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3003 = (segment_000000_pm_final pmStore) 3003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 5)) 3003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5003 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).2 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 3003)).2 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hViewSm(smStore:Store):(segment_000000_sm_final smStore) 110=fw_view [1, 16, 64] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 2) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 100], outs := [110], params := [1, 16, 64] }] ++ (segment_000000_sm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 110 = fw_view [1, 16, 64] (((segment_000000_sm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ColumnDwCase5_0.smGraph smStore
      (segment_000000_sm_nodes.take 2) (segment_000000_sm_nodes.drop 3)
      { rank := 0, op := "OpName.BW_view", ins := [100, 100], outs := [110], params := [1, 16, 64] } 110
      (fun t => fw_view [1, 16, 64] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ColumnDwCase5_0.smGraph t 0 1 [16, 64] 100 100 110
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.smGraph smStore
      (segment_000000_sm_nodes.take 2) ({ rank := 0, op := "OpName.BW_view", ins := [100, 100], outs := [110], params := [1, 16, 64] } :: (segment_000000_sm_nodes.drop 3)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 110 = fw_view [1, 16, 64] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [1, 16, 64] (((segment_000000_sm_nodes.take 2)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.smGraph) smStore 100) := hout_prefix
      _ = fw_view [1, 16, 64] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hViewPm(pmStore:Store):(segment_000000_pm_final pmStore) 1100=fw_view [1, 16, 64] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 1000], outs := [1100], params := [1, 16, 64] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 1100 = fw_view [1, 16, 64] (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 1000], outs := [1100], params := [1, 16, 64] } 1100
      (fun t => fw_view [1, 16, 64] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ColumnDwCase5_0.pmGraph t 0 1 [16, 64] 1000 1000 1100
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ColumnDwCase5_0.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 1000], outs := [1100], params := [1, 16, 64] } :: (segment_000000_pm_nodes.drop 6)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 1100 = fw_view [1, 16, 64] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [1, 16, 64] (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful ColumnDwCase5_0.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [1, 16, 64] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_dw_shape (g x w : Tensor) (o i : Nat)
    (hg : g.shape = [1,16,o]) (hx : x.shape = [1,16,i])
    (hw : w.shape = [o,i]) : (bw_linear g x w).2.shape = [o,i] :=
  bw_linear_3d_snd_shape 1 16 o i g x w hg hx hw

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
    have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
    change smFinal 100 = pmFinal 1000 ∧
      (smFinal 100).shape = [1, 16, 64] ∧
      (pmFinal 1000).shape = [1, 16, 64] at hg
    have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 2 [1, 16, 64] [1, 16, 16] at hx
    have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 1 [64, 64] [64, 16] at hw
    have hxValue : smFinal 200 = allGatherPrimDimN 2 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hwValue : smFinal 300 = allGatherPrimDimN 1 4 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] := by
      simpa only [List.length_cons, List.length_nil] using hw.full_value
    have hSmWriter : smFinal 401 =
        (bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).2 :=
      segment_000000_hSmWriter smStore
    have hvi:fact_g.Holds smFinal pmFinal:=hframe _ (by native_decide)
    have hvs:=segment_000000_hViewSm smStore
    have hvp:=segment_000000_hViewPm pmStore
    change smFinal 110=fw_view [1, 16, 64] (smFinal 100) at hvs
    change pmFinal 1100=fw_view [1, 16, 64] (pmFinal 1000) at hvp
    have houtView:fact_view.Holds smFinal pmFinal:=by
      change smFinal 110=pmFinal 1100∧_∧_
      rw [hvs,hvp]
      exact JoinedRel.fw_view [1, 16, 64] [1, 16, 64] hvi
    have hPmWriter0 : pmFinal 5000 =
        (bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2 :=
      segment_000000_hPmWriter0 pmStore
    have hxShape0 := hx.shard_shapes (pmFinal 2000) (by simp)
    have hwShape0 := hw.shard_shapes (pmFinal 3000) (by simp)
    have hOutShape0 : (pmFinal 5000).shape = [64, 16] := by
      rw [hPmWriter0]
      exact segment_000000_dw_shape _ _ _ 64 16 hg.2.2 hxShape0 hwShape0
    have hPmWriter1 : pmFinal 5001 =
        (bw_linear (pmFinal 1000) (pmFinal 2001) (pmFinal 3001)).2 :=
      segment_000000_hPmWriter1 pmStore
    have hxShape1 := hx.shard_shapes (pmFinal 2001) (by simp)
    have hwShape1 := hw.shard_shapes (pmFinal 3001) (by simp)
    have hOutShape1 : (pmFinal 5001).shape = [64, 16] := by
      rw [hPmWriter1]
      exact segment_000000_dw_shape _ _ _ 64 16 hg.2.2 hxShape1 hwShape1
    have hPmWriter2 : pmFinal 5002 =
        (bw_linear (pmFinal 1000) (pmFinal 2002) (pmFinal 3002)).2 :=
      segment_000000_hPmWriter2 pmStore
    have hxShape2 := hx.shard_shapes (pmFinal 2002) (by simp)
    have hwShape2 := hw.shard_shapes (pmFinal 3002) (by simp)
    have hOutShape2 : (pmFinal 5002).shape = [64, 16] := by
      rw [hPmWriter2]
      exact segment_000000_dw_shape _ _ _ 64 16 hg.2.2 hxShape2 hwShape2
    have hPmWriter3 : pmFinal 5003 =
        (bw_linear (pmFinal 1000) (pmFinal 2003) (pmFinal 3003)).2 :=
      segment_000000_hPmWriter3 pmStore
    have hxShape3 := hx.shard_shapes (pmFinal 2003) (by simp)
    have hwShape3 := hw.shard_shapes (pmFinal 3003) (by simp)
    have hOutShape3 : (pmFinal 5003).shape = [64, 16] := by
      rw [hPmWriter3]
      exact segment_000000_dw_shape _ _ _ 64 16 hg.2.2 hxShape3 hwShape3
    have hcomm := TrainVerify.Denote.bw_linear_dw_column_allGather_rank3 4 1 16 64 16
      (pmFinal 1000) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
      hg.2.2 hx.shard_shapes hw.shard_shapes
    simp only [List.length_cons, List.length_nil, List.zipWith_cons_cons, List.zipWith_nil_left] at hcomm
    have hOutValue : smFinal 401 = allGatherPrimDimN 1 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] := by
      rw [hSmWriter, hg.1, hxValue, hwValue, hcomm]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2, ← hPmWriter3]
    have hOutValueList : smFinal 401 =
        allGatherPrimDimN 1 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003].length 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 401).shape = [64, 64] := by
      rw [hSmWriter]
      exact segment_000000_dw_shape _ _ _ 64 64 hg.2.1 hx.full_shape hw.full_shape
    have hout : fact_dw.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 401) [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 1 [64, 64] [64, 16]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := by decide
        shard_shapes := ?_
        shape_contract := by
          simp only [List.length_cons, List.length_nil]
          native_decide
      }
      intro shard hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2 | h3
      · subst shard
        exact hOutShape0
      · subst shard
        exact hOutShape1
      · subst shard
        exact hOutShape2
      · subst shard
        exact hOutShape3
    intro fact hfact
    have covered : fact ∈ [fact_dw, fact_view] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fact_dw, fact_view] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · exact hout
      · exact houtView
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate ColumnDwCase5_0.smGraph ColumnDwCase5_0.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end ColumnDwCase5_0
