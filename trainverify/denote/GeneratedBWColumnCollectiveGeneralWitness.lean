import denote.RelationCompiler
import denote.KRankBWLinearDxColumnGeneral
import denote.KRankAllToAll
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLinearDxColumn
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [600, 600], outs := [601], params := [2, 8, 32] }, { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [6000, 6001, 6002, 6003], outs := [6100], params := [2] }, { rank := 0, op := "OpName.BW_view", ins := [6100, 6100], outs := [6101], params := [2, 8, 32] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7000], params := [2, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7001], params := [2, 1] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7002], params := [2, 1] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7003], params := [2, 1] }] }
def fact_g : RelationFact := .joined 100 1000 [2, 8, 7]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 2 [2, 8, 32] [2, 8, 8]
def fact_w : RelationFact := .sharded 300 [3000, 3001, 3002, 3003] 1 [7, 32] [7, 8]
def fact_out : RelationFact := .sharded 400 [4000, 4001, 4002, 4003] 2 [2, 8, 32] [2, 8, 8]
def fact_gin : RelationFact := .sharded 600 [6000, 6001, 6002, 6003] 2 [2, 8, 32] [2, 8, 8]
def fact_gout : RelationFact := .joined 600 6100 [2, 8, 32]
def fact_view : RelationFact := .joined 601 6101 [2, 8, 32]
def fact_aout : RelationFact := .sharded 400 [7000, 7001, 7002, 7003] 1 [2, 8, 32] [2, 2, 32]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_gin]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_view, fact_aout]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_view", ins := [600, 600], outs := [601], params := [2, 8, 32] }, { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [6000, 6001, 6002, 6003], outs := [6100], params := [2] }, { rank := 0, op := "OpName.BW_view", ins := [6100, 6100], outs := [6101], params := [2, 8, 32] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7000], params := [2, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7001], params := [2, 1] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7002], params := [2, 1] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7003], params := [2, 1] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store:=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store:=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) z

private theorem segment_000000_hLinearSm(smStore:Store):(segment_000000_sm_final smStore) 400=(bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_linear (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 200) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_linear (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxColumn.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 2)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 2)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_linear (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 100) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 200) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hLinearPm0(pmStore:Store):(segment_000000_pm_final pmStore) 4000=(bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_linear (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxColumn.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hLinearPm1(pmStore:Store):(segment_000000_pm_final pmStore) 4001=(bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3001)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] } 4001
      (fun t => (bw_linear (t 1000) (t 2001) (t 3001)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxColumn.pmGraph t 1 1000 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1000, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3001)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hLinearPm2(pmStore:Store):(segment_000000_pm_final pmStore) 4002=(bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3002)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] } 4002
      (fun t => (bw_linear (t 1000) (t 2002) (t 3002)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxColumn.pmGraph t 2 1000 2002 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1000, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3002)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hLinearPm3(pmStore:Store):(segment_000000_pm_final pmStore) 4003=(bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4003 = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3003)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] } 4003
      (fun t => (bw_linear (t 1000) (t 2003) (t 3003)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out SyntheticBWLinearDxColumn.pmGraph t 3 1000 2003 3003 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3003 = (segment_000000_pm_final pmStore) 3003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1000, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4003 = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).1 := by
    calc
      _ = (bw_linear (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 3003)).1 := hout_prefix
      _ = (bw_linear ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hGatherPm(pmStore:Store):(segment_000000_pm_final pmStore) 6100=allGatherPrimDimN 2 4 0 [(segment_000000_pm_final pmStore) 6000, (segment_000000_pm_final pmStore) 6001, (segment_000000_pm_final pmStore) 6002, (segment_000000_pm_final pmStore) 6003]:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [6000, 6001, 6002, 6003], outs := [6100], params := [2] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 6100 = allGatherPrimDimN 2 4 0 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6000, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6001, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6002, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6003] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 0, op := "OpName.AllGatherPrim", ins := [6000, 6001, 6002, 6003], outs := [6100], params := [2] } 6100
      (fun t => allGatherPrimDimN 2 4 0 [t 6000, t 6001, t 6002, t 6003]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_allGatherPrimDimN_out SyntheticBWLinearDxColumn.pmGraph t 0 [6000, 6001, 6002, 6003] 6100 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6000 = (segment_000000_pm_final pmStore) 6000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.AllGatherPrim", ins := [6000, 6001, 6002, 6003], outs := [6100], params := [2] } :: (segment_000000_pm_nodes.drop 5)) 6000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6001 = (segment_000000_pm_final pmStore) 6001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.AllGatherPrim", ins := [6000, 6001, 6002, 6003], outs := [6100], params := [2] } :: (segment_000000_pm_nodes.drop 5)) 6001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6002 = (segment_000000_pm_final pmStore) 6002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.AllGatherPrim", ins := [6000, 6001, 6002, 6003], outs := [6100], params := [2] } :: (segment_000000_pm_nodes.drop 5)) 6002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6003 = (segment_000000_pm_final pmStore) 6003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.AllGatherPrim", ins := [6000, 6001, 6002, 6003], outs := [6100], params := [2] } :: (segment_000000_pm_nodes.drop 5)) 6003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 6100 = allGatherPrimDimN 2 4 0 [(segment_000000_pm_final pmStore) 6000, (segment_000000_pm_final pmStore) 6001, (segment_000000_pm_final pmStore) 6002, (segment_000000_pm_final pmStore) 6003] := by
    calc
      _ = allGatherPrimDimN 2 4 0 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6000, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6001, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6002, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6003] := hout_prefix
      _ = allGatherPrimDimN 2 4 0 [(segment_000000_pm_final pmStore) 6000, (segment_000000_pm_final pmStore) 6001, (segment_000000_pm_final pmStore) 6002, (segment_000000_pm_final pmStore) 6003] := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hViewSm(smStore:Store):(segment_000000_sm_final smStore) 601=fw_view [2, 8, 32] ((segment_000000_sm_final smStore) 600):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [600, 600], outs := [601], params := [2, 8, 32] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 601 = fw_view [2, 8, 32] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 600) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [600, 600], outs := [601], params := [2, 8, 32] } 601
      (fun t => fw_view [2, 8, 32] (t 600)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out SyntheticBWLinearDxColumn.smGraph t 0 2 [8, 32] 600 600 601
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 600 = (segment_000000_sm_final smStore) 600 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [600, 600], outs := [601], params := [2, 8, 32] } :: (segment_000000_sm_nodes.drop 1)) 600
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 601 = fw_view [2, 8, 32] ((segment_000000_sm_final smStore) 600) := by
    calc
      _ = fw_view [2, 8, 32] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.smGraph) smStore 600) := hout_prefix
      _ = fw_view [2, 8, 32] ((segment_000000_sm_final smStore) 600) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hViewPm(pmStore:Store):(segment_000000_pm_final pmStore) 6101=fw_view [2, 8, 32] ((segment_000000_pm_final pmStore) 6100):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 0, op := "OpName.BW_view", ins := [6100, 6100], outs := [6101], params := [2, 8, 32] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 6101 = fw_view [2, 8, 32] (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 0, op := "OpName.BW_view", ins := [6100, 6100], outs := [6101], params := [2, 8, 32] } 6101
      (fun t => fw_view [2, 8, 32] (t 6100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out SyntheticBWLinearDxColumn.pmGraph t 0 2 [8, 32] 6100 6100 6101
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6100 = (segment_000000_pm_final pmStore) 6100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 0, op := "OpName.BW_view", ins := [6100, 6100], outs := [6101], params := [2, 8, 32] } :: (segment_000000_pm_nodes.drop 6)) 6100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 6101 = fw_view [2, 8, 32] ((segment_000000_pm_final pmStore) 6100) := by
    calc
      _ = fw_view [2, 8, 32] (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 6100) := hout_prefix
      _ = fw_view [2, 8, 32] ((segment_000000_pm_final pmStore) 6100) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hA2APm0(pmStore:Store):(segment_000000_pm_final pmStore) 7000=allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 0 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 6) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7000], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7000 = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 0 [((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) (segment_000000_pm_nodes.drop 7)
      { rank := 0, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7000], params := [2, 1] } 7000
      (fun t => allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 0 [t 4000, t 4001, t 4002, t 4003] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out SyntheticBWLinearDxColumn.pmGraph t 0 [4000, 4001, 4002, 4003] 7000 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000 = (segment_000000_pm_final pmStore) 4000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7000], params := [2, 1] } :: (segment_000000_pm_nodes.drop 7)) 4000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001 = (segment_000000_pm_final pmStore) 4001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7000], params := [2, 1] } :: (segment_000000_pm_nodes.drop 7)) 4001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002 = (segment_000000_pm_final pmStore) 4002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7000], params := [2, 1] } :: (segment_000000_pm_nodes.drop 7)) 4002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003 = (segment_000000_pm_final pmStore) 4003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7000], params := [2, 1] } :: (segment_000000_pm_nodes.drop 7)) 4003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7000 = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 0 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1 := by
    calc
      _ = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 0 [((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003] 2 1 := hout_prefix
      _ = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 0 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hA2APm1(pmStore:Store):(segment_000000_pm_final pmStore) 7001=allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 1 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7001], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7001 = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 1 [((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000, ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001, ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002, ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 1, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7001], params := [2, 1] } 7001
      (fun t => allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 1 [t 4000, t 4001, t 4002, t 4003] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out SyntheticBWLinearDxColumn.pmGraph t 1 [4000, 4001, 4002, 4003] 7001 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000 = (segment_000000_pm_final pmStore) 4000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7001], params := [2, 1] } :: (segment_000000_pm_nodes.drop 8)) 4000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001 = (segment_000000_pm_final pmStore) 4001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7001], params := [2, 1] } :: (segment_000000_pm_nodes.drop 8)) 4001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002 = (segment_000000_pm_final pmStore) 4002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7001], params := [2, 1] } :: (segment_000000_pm_nodes.drop 8)) 4002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003 = (segment_000000_pm_final pmStore) 4003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7001], params := [2, 1] } :: (segment_000000_pm_nodes.drop 8)) 4003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7001 = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 1 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1 := by
    calc
      _ = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 1 [((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000, ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001, ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002, ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003] 2 1 := hout_prefix
      _ = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 1 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hA2APm2(pmStore:Store):(segment_000000_pm_final pmStore) 7002=allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 2 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 8) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7002], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7002 = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 2 [((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000, ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001, ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002, ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) (segment_000000_pm_nodes.drop 9)
      { rank := 2, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7002], params := [2, 1] } 7002
      (fun t => allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 2 [t 4000, t 4001, t 4002, t 4003] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out SyntheticBWLinearDxColumn.pmGraph t 2 [4000, 4001, 4002, 4003] 7002 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000 = (segment_000000_pm_final pmStore) 4000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7002], params := [2, 1] } :: (segment_000000_pm_nodes.drop 9)) 4000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001 = (segment_000000_pm_final pmStore) 4001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7002], params := [2, 1] } :: (segment_000000_pm_nodes.drop 9)) 4001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002 = (segment_000000_pm_final pmStore) 4002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7002], params := [2, 1] } :: (segment_000000_pm_nodes.drop 9)) 4002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003 = (segment_000000_pm_final pmStore) 4003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7002], params := [2, 1] } :: (segment_000000_pm_nodes.drop 9)) 4003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7002 = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 2 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1 := by
    calc
      _ = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 2 [((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000, ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001, ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002, ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003] 2 1 := hout_prefix
      _ = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 2 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hA2APm3(pmStore:Store):(segment_000000_pm_final pmStore) 7003=allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 3 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 9) ++ [{ rank := 3, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7003], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 10) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7003 = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 3 [((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000, ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001, ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002, ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 9) (segment_000000_pm_nodes.drop 10)
      { rank := 3, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7003], params := [2, 1] } 7003
      (fun t => allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 3 [t 4000, t 4001, t 4002, t 4003] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out SyntheticBWLinearDxColumn.pmGraph t 3 [4000, 4001, 4002, 4003] 7003 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000 = (segment_000000_pm_final pmStore) 4000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7003], params := [2, 1] } :: (segment_000000_pm_nodes.drop 10)) 4000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001 = (segment_000000_pm_final pmStore) 4001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7003], params := [2, 1] } :: (segment_000000_pm_nodes.drop 10)) 4001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002 = (segment_000000_pm_final pmStore) 4002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7003], params := [2, 1] } :: (segment_000000_pm_nodes.drop 10)) 4002
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003 = (segment_000000_pm_final pmStore) 4003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLinearDxColumn.pmGraph pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [4000, 4001, 4002, 4003], outs := [7003], params := [2, 1] } :: (segment_000000_pm_nodes.drop 10)) 4003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7003 = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 3 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1 := by
    calc
      _ = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 3 [((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4000, ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4001, ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4002, ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful SyntheticBWLinearDxColumn.pmGraph) pmStore 4003] 2 1 := hout_prefix
      _ = allToAllPrimWithDims SyntheticBWLinearDxColumn.pmGraph.numRanks 3 [(segment_000000_pm_final pmStore) 4000, (segment_000000_pm_final pmStore) 4001, (segment_000000_pm_final pmStore) 4002, (segment_000000_pm_final pmStore) 4003] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_dx_shape(g x w:Tensor)(o i:Nat)(hg:g.shape=[2,8,o])(hx:x.shape=[2,8,i])(hw:w.shape=[o,i]):(bw_linear g x w).1.shape=[2,8,i]:=bw_linear_3d_fst_shape 2 8 o i g x w hg hx hw
set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_000000.Holds smStore pmStore) : state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
 let smFinal:=segment_000000_sm_final smStore
 let pmFinal:=segment_000000_pm_final pmStore
 have hframe:state_000000.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final;apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
 have hg:fact_g.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change smFinal 100=pmFinal 1000∧(smFinal 100).shape=[2, 8, 7]∧(pmFinal 1000).shape=[2, 8, 7] at hg
 have hx:fact_x.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 2 [2, 8, 32] [2, 8, 8] at hx
 have hw:fact_w.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 1 [7, 32] [7, 8] at hw
 have hxV:smFinal 200=allGatherPrimDimN 2 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
 have hwV:smFinal 300=allGatherPrimDimN 1 4 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003]:=by simpa only [List.length_cons,List.length_nil] using hw.full_value
 have hLs:=segment_000000_hLinearSm smStore
 change smFinal 400=(bw_linear (smFinal 100) (smFinal 200) (smFinal 300)).1 at hLs
 have hLp0:=segment_000000_hLinearPm0 pmStore
 change pmFinal 4000=(bw_linear (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1 at hLp0
 have hxS0:=hx.shard_shapes (pmFinal 2000) (by simp)
 have hwS0:=hw.shard_shapes (pmFinal 3000) (by simp)
 have hoS0:(pmFinal 4000).shape=[2, 8, 8]:=by rw [hLp0];exact segment_000000_dx_shape _ _ _ 7 8 hg.2.2 hxS0 hwS0
 have hLp1:=segment_000000_hLinearPm1 pmStore
 change pmFinal 4001=(bw_linear (pmFinal 1000) (pmFinal 2001) (pmFinal 3001)).1 at hLp1
 have hxS1:=hx.shard_shapes (pmFinal 2001) (by simp)
 have hwS1:=hw.shard_shapes (pmFinal 3001) (by simp)
 have hoS1:(pmFinal 4001).shape=[2, 8, 8]:=by rw [hLp1];exact segment_000000_dx_shape _ _ _ 7 8 hg.2.2 hxS1 hwS1
 have hLp2:=segment_000000_hLinearPm2 pmStore
 change pmFinal 4002=(bw_linear (pmFinal 1000) (pmFinal 2002) (pmFinal 3002)).1 at hLp2
 have hxS2:=hx.shard_shapes (pmFinal 2002) (by simp)
 have hwS2:=hw.shard_shapes (pmFinal 3002) (by simp)
 have hoS2:(pmFinal 4002).shape=[2, 8, 8]:=by rw [hLp2];exact segment_000000_dx_shape _ _ _ 7 8 hg.2.2 hxS2 hwS2
 have hLp3:=segment_000000_hLinearPm3 pmStore
 change pmFinal 4003=(bw_linear (pmFinal 1000) (pmFinal 2003) (pmFinal 3003)).1 at hLp3
 have hxS3:=hx.shard_shapes (pmFinal 2003) (by simp)
 have hwS3:=hw.shard_shapes (pmFinal 3003) (by simp)
 have hoS3:(pmFinal 4003).shape=[2, 8, 8]:=by rw [hLp3];exact segment_000000_dx_shape _ _ _ 7 8 hg.2.2 hxS3 hwS3
 have hcomm := TrainVerify.Denote.bw_linear_dx_column_allGather_rank3 4 2 8 7 8
   (pmFinal 1000) (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003]
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
   hg.2.2 hx.full_shape hx.shard_shapes hw.shard_shapes
 simp only [List.zipWith_cons_cons, List.zipWith_nil_left] at hcomm
 have hLV:smFinal 400=allGatherPrimDimN 2 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003]:=by rw [hLs,hg.1,hwV,hcomm];rw [←hLp0, ←hLp1, ←hLp2, ←hLp3]
 have hLVL:smFinal 400=allGatherPrimDimN 2 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003].length 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003]:=by simpa only [List.length_cons,List.length_nil] using hLV
 have hLF:(smFinal 400).shape=[2, 8, 32]:=by rw [hLs];exact segment_000000_dx_shape _ _ _ 7 32 hg.2.1 hx.full_shape hw.full_shape
 have hLShapes:∀ shard∈[pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003],shard.shape=[2, 8, 8]:=by
  simp only [List.forall_mem_cons]
  exact ⟨hoS0, hoS1, hoS2, hoS3, List.forall_mem_nil _⟩
 have houtL:fact_out.Holds smFinal pmFinal:=by exact {full_value:=hLVL,full_shape:=hLF,shards_nonempty:=List.cons_ne_nil _ _,gather_dim_lt:=by native_decide,shard_shapes:=hLShapes,shape_contract:=by simp only [List.map, List.length_cons,List.length_nil];native_decide}
 have hgi:fact_gin.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 600) [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003] 2 [2, 8, 32] [2, 8, 8] at hgi
 have hGw:=segment_000000_hGatherPm pmStore
 change pmFinal 6100=allGatherPrimDimN 2 4 0 [pmFinal 6000, pmFinal 6001, pmFinal 6002, pmFinal 6003] at hGw
 have hGEq:smFinal 600=pmFinal 6100:=(ShardedRel.to_joined_allGather hgi).trans hGw.symm
 have houtG:fact_gout.Holds smFinal pmFinal:=by exact ⟨hGEq,hgi.full_shape,by rw [←hGEq];exact hgi.full_shape⟩
 have hVs:=segment_000000_hViewSm smStore
 change smFinal 601=fw_view [2, 8, 32] (smFinal 600) at hVs
 have hVp:=segment_000000_hViewPm pmStore
 change pmFinal 6101=fw_view [2, 8, 32] (pmFinal 6100) at hVp
 have houtV:fact_view.Holds smFinal pmFinal:=by change smFinal 601=pmFinal 6101∧_∧_;rw [hVs,hVp];exact JoinedRel.fw_view [2, 8, 32] [2, 8, 32] houtG
 have hA0:=segment_000000_hA2APm0 pmStore
 change pmFinal 7000=allToAllPrimWithDims 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 1 at hA0
 have hA1:=segment_000000_hA2APm1 pmStore
 change pmFinal 7001=allToAllPrimWithDims 4 1 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 1 at hA1
 have hA2:=segment_000000_hA2APm2 pmStore
 change pmFinal 7002=allToAllPrimWithDims 4 2 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 1 at hA2
 have hA3:=segment_000000_hA2APm3 pmStore
 change pmFinal 7003=allToAllPrimWithDims 4 3 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 1 at hA3
 have hHead:(([pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003].head?.map (fun t => t.shape)).getD [])=[2, 8, 8]:=houtL.shard_shapes _ (by simp)
 have hAV:smFinal 400=allGatherPrimDimN 2 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003]:=by simpa only [List.map,List.length_cons,List.length_nil] using houtL.full_value
 have hGS:(allGatherPrimDimN 2 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003]).shape=[2, 8, 32]:=by rw [←hAV];exact houtL.full_shape
 have hOd:1<(allGatherPrimDimN 2 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003]).shape.length:=by rw [hGS];native_decide
 have hDv:(allGatherPrimDimN 2 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003]).shape.getD 1 0%4=0:=by rw [hGS];native_decide
 have hAS0:(pmFinal 7000).shape=[2, 2, 32]:=by rw [hA0,allToAllPrimWithDims_shape 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 1 [2, 8, 8] hHead (by native_decide)];native_decide
 have hAS1:(pmFinal 7001).shape=[2, 2, 32]:=by rw [hA1,allToAllPrimWithDims_shape 4 1 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 1 [2, 8, 8] hHead (by native_decide)];native_decide
 have hAS2:(pmFinal 7002).shape=[2, 2, 32]:=by rw [hA2,allToAllPrimWithDims_shape 4 2 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 1 [2, 8, 8] hHead (by native_decide)];native_decide
 have hAS3:(pmFinal 7003).shape=[2, 2, 32]:=by rw [hA3,allToAllPrimWithDims_shape 4 3 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 1 [2, 8, 8] hHead (by native_decide)];native_decide
 have hOrd:[pmFinal 7000, pmFinal 7001, pmFinal 7002, pmFinal 7003]=List.ofFn (fun r : Fin 4 => allToAllPrimWithDims 4 r.1 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 1):=by rw [hA0, hA1, hA2, hA3];rfl
 have hAC:allGatherPrimDimN 1 [pmFinal 7000, pmFinal 7001, pmFinal 7002, pmFinal 7003].length 0 [pmFinal 7000, pmFinal 7001, pmFinal 7002, pmFinal 7003]=allGatherPrimDimN 2 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003]:=by rw [hOrd];simpa only [List.length_cons,List.length_nil,List.length_ofFn] using (TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 2 1 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] (by simp) hOd hDv)
 have hAShapes:∀ shard∈[pmFinal 7000, pmFinal 7001, pmFinal 7002, pmFinal 7003],shard.shape=[2, 2, 32]:=by
  simp only [List.forall_mem_cons]
  exact ⟨hAS0, hAS1, hAS2, hAS3, List.forall_mem_nil _⟩
 have houtA:fact_aout.Holds smFinal pmFinal:=by exact {full_value:=by simp only [List.map];rw [hAC];exact hAV,full_shape:=houtL.full_shape,shards_nonempty:=List.cons_ne_nil _ _,gather_dim_lt:=by native_decide,shard_shapes:=hAShapes,shape_contract:=by simp only [List.map, List.length_cons,List.length_nil];native_decide}
 intro fact hfact
 have hc:fact∈[fact_out, fact_gout, fact_view, fact_aout]++state_000000.facts:=by exact (show state_000001.facts⊆[fact_out, fact_gout, fact_view, fact_aout]++state_000000.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh|old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
   rcases fresh with rfl | rfl | rfl | rfl
   · exact houtL
   · exact houtG
   · exact houtV
   · exact houtA
 · exact hframe fact old

set_option maxRecDepth 32768 in
private def segment_000000:ClosedDepSegmentCertificate SyntheticBWLinearDxColumn.smGraph SyntheticBWLinearDxColumn.pmGraph state_000000 state_000001 where
 smNodes:=segment_000000_sm_nodes
 pmNodes:=segment_000000_pm_nodes
 sound:=by intro smStore pmStore hstate;have h:=segment_000000_sound smStore pmStore hstate;unfold segment_000000_sm_final segment_000000_pm_final at h;exact h

#print axioms segment_000000
end
end SyntheticBWLinearDxColumn
