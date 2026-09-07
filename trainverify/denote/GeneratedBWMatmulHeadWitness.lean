import denote.RelationCompiler
import denote.KRankBWMatmulHead
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulHeadCase0
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001] 1 [1, 4, 16, 16] [1, 2, 16, 16]
def fact_x : RelationFact := .sharded 200 [2000, 2001] 1 [1, 4, 16, 16] [1, 2, 16, 16]
def fact_y : RelationFact := .sharded 300 [3000, 3001] 1 [1, 4, 16, 16] [1, 2, 16, 16]
def fact_out0 : RelationFact := .sharded 400 [4000, 4001] 1 [1, 4, 16, 16] [1, 2, 16, 16]
def fact_out1 : RelationFact := .sharded 401 [5000, 5001] 1 [1, 4, 16, 16] [1, 2, 16, 16]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_out0, fact_out1]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }]
@[irreducible] private def segment_000000_sm_final(s:Store):Store:=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) s
@[irreducible] private def segment_000000_pm_final(s:Store):Store:=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) s
private theorem segment_000000_hSm0(smStore:Store):(segment_000000_sm_final smStore) 400=(bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase0.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_0(pmStore:Store):(segment_000000_pm_final pmStore) 4000=(bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase0.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_1(pmStore:Store):(segment_000000_pm_final pmStore) 4001=(bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3001)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } 4001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3001)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase0.pmGraph t 1 1001 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3001)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hSm1(smStore:Store):(segment_000000_sm_final smStore) 401=(bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase0.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_0(pmStore:Store):(segment_000000_pm_final pmStore) 5000=(bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase0.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_1(pmStore:Store):(segment_000000_pm_final pmStore) 5001=(bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3001)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } 5001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3001)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase0.pmGraph t 1 1001 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase0.pmGraph) pmStore 3001)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_transpose_shape (t:Tensor)(a b c d:Nat)(ht:t.shape=[a,b,c,d]):(transpose2d t).shape=[a,b,d,c]:=by
  simp only [transpose2d,ht,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,Tensor.mkShape]
set_option maxHeartbeats 500000 in
private theorem segment_000000_sound(smStore pmStore:Store)(hstate:state_000000.Holds smStore pmStore):state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore):=by
  let smFinal:=segment_000000_sm_final smStore
  let pmFinal:=segment_000000_pm_final pmStore
  have hframe:state_000000.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final;apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg:fact_g.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001] 1 [1, 4, 16, 16] [1, 2, 16, 16] at hg
  have hgV:smFinal 100=allGatherPrimDimN 1 2 0 [pmFinal 1000, pmFinal 1001]:=by simpa only [List.length_cons,List.length_nil] using hg.full_value
  have hx:fact_x.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001] 1 [1, 4, 16, 16] [1, 2, 16, 16] at hx
  have hxV:smFinal 200=allGatherPrimDimN 1 2 0 [pmFinal 2000, pmFinal 2001]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
  have hy:fact_y.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001] 1 [1, 4, 16, 16] [1, 2, 16, 16] at hy
  have hyV:smFinal 300=allGatherPrimDimN 1 2 0 [pmFinal 3000, pmFinal 3001]:=by simpa only [List.length_cons,List.length_nil] using hy.full_value
  have hS0:smFinal 400=(bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).1:=segment_000000_hSm0 smStore
  have hP0_0:pmFinal 4000=(bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1:=segment_000000_hPm0_0 pmStore
  have hP0_1:pmFinal 4001=(bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3001)).1:=segment_000000_hPm0_1 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP0_0
  simp only [bw_matmul,batchedMatmulBwd] at hP0_1
  have hC0:=TrainVerify.Denote.bw_matmul_fst_head_gather_rank4 2 1 2 16 16 16 [pmFinal 1000, pmFinal 1001] [pmFinal 2000, pmFinal 2001] [pmFinal 3000, pmFinal 3001]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV0:smFinal 400=allGatherPrimDimN 1 2 0 [pmFinal 4000, pmFinal 4001]:=by
    rw [hS0,hgV,hxV,hyV,hC0]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP0_0, ←hP0_1]
  have hFull0:(smFinal 400).shape=[1, 4, 16, 16]:=by rw [hS0];exact fw_matmul_rank4_shape _ _ 1 4 16 16 16 hg.full_shape (segment_000000_transpose_shape _ 1 4 16 16 hy.full_shape)
  have hout0:fact_out0.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001] 1 [1, 4, 16, 16] [1, 2, 16, 16]
    refine {full_value:=hV0,full_shape:=hFull0,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1
      · subst piece;rw [hP0_0];exact fw_matmul_rank4_shape _ _ 1 2 16 16 16 (hg.shard_shapes (pmFinal 1000) (by simp)) (segment_000000_transpose_shape _ 1 2 16 16 (hy.shard_shapes (pmFinal 3000) (by simp)))
      · subst piece;rw [hP0_1];exact fw_matmul_rank4_shape _ _ 1 2 16 16 16 (hg.shard_shapes (pmFinal 1001) (by simp)) (segment_000000_transpose_shape _ 1 2 16 16 (hy.shard_shapes (pmFinal 3001) (by simp)))
    · simp only [List.length_cons,List.length_nil];native_decide
  have hS1:smFinal 401=(bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).2:=segment_000000_hSm1 smStore
  have hP1_0:pmFinal 5000=(bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2:=segment_000000_hPm1_0 pmStore
  have hP1_1:pmFinal 5001=(bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3001)).2:=segment_000000_hPm1_1 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP1_0
  simp only [bw_matmul,batchedMatmulBwd] at hP1_1
  have hC1:=TrainVerify.Denote.bw_matmul_snd_head_gather_rank4 2 1 2 16 16 16 [pmFinal 1000, pmFinal 1001] [pmFinal 2000, pmFinal 2001] [pmFinal 3000, pmFinal 3001]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV1:smFinal 401=allGatherPrimDimN 1 2 0 [pmFinal 5000, pmFinal 5001]:=by
    rw [hS1,hgV,hxV,hyV,hC1]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP1_0, ←hP1_1]
  have hFull1:(smFinal 401).shape=[1, 4, 16, 16]:=by rw [hS1];exact fw_matmul_rank4_shape _ _ 1 4 16 16 16 (segment_000000_transpose_shape _ 1 4 16 16 hx.full_shape) hg.full_shape
  have hout1:fact_out1.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 401) [pmFinal 5000, pmFinal 5001] 1 [1, 4, 16, 16] [1, 2, 16, 16]
    refine {full_value:=hV1,full_shape:=hFull1,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1
      · subst piece;rw [hP1_0];exact fw_matmul_rank4_shape _ _ 1 2 16 16 16 (segment_000000_transpose_shape _ 1 2 16 16 (hx.shard_shapes (pmFinal 2000) (by simp))) (hg.shard_shapes (pmFinal 1000) (by simp))
      · subst piece;rw [hP1_1];exact fw_matmul_rank4_shape _ _ 1 2 16 16 16 (segment_000000_transpose_shape _ 1 2 16 16 (hx.shard_shapes (pmFinal 2001) (by simp))) (hg.shard_shapes (pmFinal 1001) (by simp))
    · simp only [List.length_cons,List.length_nil];native_decide
  intro fact hfact
  have hc:fact∈[fact_out0, fact_out1]++state_000000.facts:=(show state_000001.facts⊆[fact_out0, fact_out1]++state_000000.facts by native_decide) hfact
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with (rfl | rfl) | old
  · exact hout0
  · exact hout1
  · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate MatmulHeadCase0.smGraph MatmulHeadCase0.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore h;have hh:=segment_000000_sound smStore pmStore h;unfold segment_000000_sm_final segment_000000_pm_final at hh;exact hh

#print axioms segment_000000
end
end MatmulHeadCase0
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulHeadCase1
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 6, 5, 11] [2, 2, 5, 11]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002] 1 [2, 6, 5, 7] [2, 2, 5, 7]
def fact_y : RelationFact := .sharded 300 [3000, 3001, 3002] 1 [2, 6, 7, 11] [2, 2, 7, 11]
def fact_out0 : RelationFact := .sharded 400 [4000, 4001, 4002] 1 [2, 6, 5, 7] [2, 2, 5, 7]
def fact_out1 : RelationFact := .sharded 401 [5000, 5001, 5002] 1 [2, 6, 7, 11] [2, 2, 7, 11]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_out0, fact_out1]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }]
@[irreducible] private def segment_000000_sm_final(s:Store):Store:=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) s
@[irreducible] private def segment_000000_pm_final(s:Store):Store:=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) s
private theorem segment_000000_hSm0(smStore:Store):(segment_000000_sm_final smStore) 400=(bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase1.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_0(pmStore:Store):(segment_000000_pm_final pmStore) 4000=(bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase1.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_1(pmStore:Store):(segment_000000_pm_final pmStore) 4001=(bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3001)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } 4001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3001)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase1.pmGraph t 1 1001 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3001)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_2(pmStore:Store):(segment_000000_pm_final pmStore) 4002=(bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3002)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } 4002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3002)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase1.pmGraph t 2 1002 2002 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3002)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hSm1(smStore:Store):(segment_000000_sm_final smStore) 401=(bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase1.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_0(pmStore:Store):(segment_000000_pm_final pmStore) 5000=(bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase1.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_1(pmStore:Store):(segment_000000_pm_final pmStore) 5001=(bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3001)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } 5001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3001)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase1.pmGraph t 1 1001 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3001)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_2(pmStore:Store):(segment_000000_pm_final pmStore) 5002=(bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3002)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } 5002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3002)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase1.pmGraph t 2 1002 2002 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase1.pmGraph) pmStore 3002)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_transpose_shape (t:Tensor)(a b c d:Nat)(ht:t.shape=[a,b,c,d]):(transpose2d t).shape=[a,b,d,c]:=by
  simp only [transpose2d,ht,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,Tensor.mkShape]
set_option maxHeartbeats 500000 in
private theorem segment_000000_sound(smStore pmStore:Store)(hstate:state_000000.Holds smStore pmStore):state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore):=by
  let smFinal:=segment_000000_sm_final smStore
  let pmFinal:=segment_000000_pm_final pmStore
  have hframe:state_000000.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final;apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg:fact_g.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 1 [2, 6, 5, 11] [2, 2, 5, 11] at hg
  have hgV:smFinal 100=allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002]:=by simpa only [List.length_cons,List.length_nil] using hg.full_value
  have hx:fact_x.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 1 [2, 6, 5, 7] [2, 2, 5, 7] at hx
  have hxV:smFinal 200=allGatherPrimDimN 1 3 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
  have hy:fact_y.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002] 1 [2, 6, 7, 11] [2, 2, 7, 11] at hy
  have hyV:smFinal 300=allGatherPrimDimN 1 3 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002]:=by simpa only [List.length_cons,List.length_nil] using hy.full_value
  have hS0:smFinal 400=(bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).1:=segment_000000_hSm0 smStore
  have hP0_0:pmFinal 4000=(bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1:=segment_000000_hPm0_0 pmStore
  have hP0_1:pmFinal 4001=(bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3001)).1:=segment_000000_hPm0_1 pmStore
  have hP0_2:pmFinal 4002=(bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3002)).1:=segment_000000_hPm0_2 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP0_0
  simp only [bw_matmul,batchedMatmulBwd] at hP0_1
  simp only [bw_matmul,batchedMatmulBwd] at hP0_2
  have hC0:=TrainVerify.Denote.bw_matmul_fst_head_gather_rank4 3 2 2 5 7 11 [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] [pmFinal 3000, pmFinal 3001, pmFinal 3002]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV0:smFinal 400=allGatherPrimDimN 1 3 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002]:=by
    rw [hS0,hgV,hxV,hyV,hC0]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP0_0, ←hP0_1, ←hP0_2]
  have hFull0:(smFinal 400).shape=[2, 6, 5, 7]:=by rw [hS0];exact fw_matmul_rank4_shape _ _ 2 6 5 11 7 hg.full_shape (segment_000000_transpose_shape _ 2 6 7 11 hy.full_shape)
  have hout0:fact_out0.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002] 1 [2, 6, 5, 7] [2, 2, 5, 7]
    refine {full_value:=hV0,full_shape:=hFull0,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1 | hh2
      · subst piece;rw [hP0_0];exact fw_matmul_rank4_shape _ _ 2 2 5 11 7 (hg.shard_shapes (pmFinal 1000) (by simp)) (segment_000000_transpose_shape _ 2 2 7 11 (hy.shard_shapes (pmFinal 3000) (by simp)))
      · subst piece;rw [hP0_1];exact fw_matmul_rank4_shape _ _ 2 2 5 11 7 (hg.shard_shapes (pmFinal 1001) (by simp)) (segment_000000_transpose_shape _ 2 2 7 11 (hy.shard_shapes (pmFinal 3001) (by simp)))
      · subst piece;rw [hP0_2];exact fw_matmul_rank4_shape _ _ 2 2 5 11 7 (hg.shard_shapes (pmFinal 1002) (by simp)) (segment_000000_transpose_shape _ 2 2 7 11 (hy.shard_shapes (pmFinal 3002) (by simp)))
    · simp only [List.length_cons,List.length_nil];native_decide
  have hS1:smFinal 401=(bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).2:=segment_000000_hSm1 smStore
  have hP1_0:pmFinal 5000=(bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2:=segment_000000_hPm1_0 pmStore
  have hP1_1:pmFinal 5001=(bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3001)).2:=segment_000000_hPm1_1 pmStore
  have hP1_2:pmFinal 5002=(bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3002)).2:=segment_000000_hPm1_2 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP1_0
  simp only [bw_matmul,batchedMatmulBwd] at hP1_1
  simp only [bw_matmul,batchedMatmulBwd] at hP1_2
  have hC1:=TrainVerify.Denote.bw_matmul_snd_head_gather_rank4 3 2 2 5 7 11 [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] [pmFinal 3000, pmFinal 3001, pmFinal 3002]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV1:smFinal 401=allGatherPrimDimN 1 3 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002]:=by
    rw [hS1,hgV,hxV,hyV,hC1]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP1_0, ←hP1_1, ←hP1_2]
  have hFull1:(smFinal 401).shape=[2, 6, 7, 11]:=by rw [hS1];exact fw_matmul_rank4_shape _ _ 2 6 7 5 11 (segment_000000_transpose_shape _ 2 6 5 7 hx.full_shape) hg.full_shape
  have hout1:fact_out1.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 401) [pmFinal 5000, pmFinal 5001, pmFinal 5002] 1 [2, 6, 7, 11] [2, 2, 7, 11]
    refine {full_value:=hV1,full_shape:=hFull1,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1 | hh2
      · subst piece;rw [hP1_0];exact fw_matmul_rank4_shape _ _ 2 2 7 5 11 (segment_000000_transpose_shape _ 2 2 5 7 (hx.shard_shapes (pmFinal 2000) (by simp))) (hg.shard_shapes (pmFinal 1000) (by simp))
      · subst piece;rw [hP1_1];exact fw_matmul_rank4_shape _ _ 2 2 7 5 11 (segment_000000_transpose_shape _ 2 2 5 7 (hx.shard_shapes (pmFinal 2001) (by simp))) (hg.shard_shapes (pmFinal 1001) (by simp))
      · subst piece;rw [hP1_2];exact fw_matmul_rank4_shape _ _ 2 2 7 5 11 (segment_000000_transpose_shape _ 2 2 5 7 (hx.shard_shapes (pmFinal 2002) (by simp))) (hg.shard_shapes (pmFinal 1002) (by simp))
    · simp only [List.length_cons,List.length_nil];native_decide
  intro fact hfact
  have hc:fact∈[fact_out0, fact_out1]++state_000000.facts:=(show state_000001.facts⊆[fact_out0, fact_out1]++state_000000.facts by native_decide) hfact
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with (rfl | rfl) | old
  · exact hout0
  · exact hout1
  · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate MatmulHeadCase1.smGraph MatmulHeadCase1.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore h;have hh:=segment_000000_sound smStore pmStore h;unfold segment_000000_sm_final segment_000000_pm_final at hh;exact hh

#print axioms segment_000000
end
end MatmulHeadCase1
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulHeadCase2
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 1 [1, 4, 16, 16] [1, 1, 16, 16]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 1 [1, 4, 16, 16] [1, 1, 16, 16]
def fact_y : RelationFact := .sharded 300 [3000, 3001, 3002, 3003] 1 [1, 4, 16, 16] [1, 1, 16, 16]
def fact_out0 : RelationFact := .sharded 400 [4000, 4001, 4002, 4003] 1 [1, 4, 16, 16] [1, 1, 16, 16]
def fact_out1 : RelationFact := .sharded 401 [5000, 5001, 5002, 5003] 1 [1, 4, 16, 16] [1, 1, 16, 16]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_out0, fact_out1]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }]
@[irreducible] private def segment_000000_sm_final(s:Store):Store:=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) s
@[irreducible] private def segment_000000_pm_final(s:Store):Store:=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) s
private theorem segment_000000_hSm0(smStore:Store):(segment_000000_sm_final smStore) 400=(bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase2.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_0(pmStore:Store):(segment_000000_pm_final pmStore) 4000=(bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase2.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_1(pmStore:Store):(segment_000000_pm_final pmStore) 4001=(bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3001)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } 4001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3001)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase2.pmGraph t 1 1001 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3001)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_2(pmStore:Store):(segment_000000_pm_final pmStore) 4002=(bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3002)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } 4002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3002)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase2.pmGraph t 2 1002 2002 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3002)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_3(pmStore:Store):(segment_000000_pm_final pmStore) 4003=(bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4003 = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3003)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } 4003
      (fun t => (bw_matmul (t 1003) (t 2003) (t 3003)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase2.pmGraph t 3 1003 2003 3003 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3003 = (segment_000000_pm_final pmStore) 3003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3003)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hSm1(smStore:Store):(segment_000000_sm_final smStore) 401=(bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase2.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_0(pmStore:Store):(segment_000000_pm_final pmStore) 5000=(bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase2.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_1(pmStore:Store):(segment_000000_pm_final pmStore) 5001=(bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3001)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } 5001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3001)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase2.pmGraph t 1 1001 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3001)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_2(pmStore:Store):(segment_000000_pm_final pmStore) 5002=(bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3002)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } 5002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3002)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase2.pmGraph t 2 1002 2002 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3002)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_3(pmStore:Store):(segment_000000_pm_final pmStore) 5003=(bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5003 = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3003)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } 5003
      (fun t => (bw_matmul (t 1003) (t 2003) (t 3003)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase2.pmGraph t 3 1003 2003 3003 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3003 = (segment_000000_pm_final pmStore) 3003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase2.pmGraph) pmStore 3003)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_transpose_shape (t:Tensor)(a b c d:Nat)(ht:t.shape=[a,b,c,d]):(transpose2d t).shape=[a,b,d,c]:=by
  simp only [transpose2d,ht,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,Tensor.mkShape]
set_option maxHeartbeats 500000 in
private theorem segment_000000_sound(smStore pmStore:Store)(hstate:state_000000.Holds smStore pmStore):state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore):=by
  let smFinal:=segment_000000_sm_final smStore
  let pmFinal:=segment_000000_pm_final pmStore
  have hframe:state_000000.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final;apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg:fact_g.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 1 [1, 4, 16, 16] [1, 1, 16, 16] at hg
  have hgV:smFinal 100=allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003]:=by simpa only [List.length_cons,List.length_nil] using hg.full_value
  have hx:fact_x.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 [1, 4, 16, 16] [1, 1, 16, 16] at hx
  have hxV:smFinal 200=allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
  have hy:fact_y.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003] 1 [1, 4, 16, 16] [1, 1, 16, 16] at hy
  have hyV:smFinal 300=allGatherPrimDimN 1 4 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003]:=by simpa only [List.length_cons,List.length_nil] using hy.full_value
  have hS0:smFinal 400=(bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).1:=segment_000000_hSm0 smStore
  have hP0_0:pmFinal 4000=(bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1:=segment_000000_hPm0_0 pmStore
  have hP0_1:pmFinal 4001=(bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3001)).1:=segment_000000_hPm0_1 pmStore
  have hP0_2:pmFinal 4002=(bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3002)).1:=segment_000000_hPm0_2 pmStore
  have hP0_3:pmFinal 4003=(bw_matmul (pmFinal 1003) (pmFinal 2003) (pmFinal 3003)).1:=segment_000000_hPm0_3 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP0_0
  simp only [bw_matmul,batchedMatmulBwd] at hP0_1
  simp only [bw_matmul,batchedMatmulBwd] at hP0_2
  simp only [bw_matmul,batchedMatmulBwd] at hP0_3
  have hC0:=TrainVerify.Denote.bw_matmul_fst_head_gather_rank4 4 1 1 16 16 16 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV0:smFinal 400=allGatherPrimDimN 1 4 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003]:=by
    rw [hS0,hgV,hxV,hyV,hC0]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP0_0, ←hP0_1, ←hP0_2, ←hP0_3]
  have hFull0:(smFinal 400).shape=[1, 4, 16, 16]:=by rw [hS0];exact fw_matmul_rank4_shape _ _ 1 4 16 16 16 hg.full_shape (segment_000000_transpose_shape _ 1 4 16 16 hy.full_shape)
  have hout0:fact_out0.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 1 [1, 4, 16, 16] [1, 1, 16, 16]
    refine {full_value:=hV0,full_shape:=hFull0,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1 | hh2 | hh3
      · subst piece;rw [hP0_0];exact fw_matmul_rank4_shape _ _ 1 1 16 16 16 (hg.shard_shapes (pmFinal 1000) (by simp)) (segment_000000_transpose_shape _ 1 1 16 16 (hy.shard_shapes (pmFinal 3000) (by simp)))
      · subst piece;rw [hP0_1];exact fw_matmul_rank4_shape _ _ 1 1 16 16 16 (hg.shard_shapes (pmFinal 1001) (by simp)) (segment_000000_transpose_shape _ 1 1 16 16 (hy.shard_shapes (pmFinal 3001) (by simp)))
      · subst piece;rw [hP0_2];exact fw_matmul_rank4_shape _ _ 1 1 16 16 16 (hg.shard_shapes (pmFinal 1002) (by simp)) (segment_000000_transpose_shape _ 1 1 16 16 (hy.shard_shapes (pmFinal 3002) (by simp)))
      · subst piece;rw [hP0_3];exact fw_matmul_rank4_shape _ _ 1 1 16 16 16 (hg.shard_shapes (pmFinal 1003) (by simp)) (segment_000000_transpose_shape _ 1 1 16 16 (hy.shard_shapes (pmFinal 3003) (by simp)))
    · simp only [List.length_cons,List.length_nil];native_decide
  have hS1:smFinal 401=(bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).2:=segment_000000_hSm1 smStore
  have hP1_0:pmFinal 5000=(bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2:=segment_000000_hPm1_0 pmStore
  have hP1_1:pmFinal 5001=(bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3001)).2:=segment_000000_hPm1_1 pmStore
  have hP1_2:pmFinal 5002=(bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3002)).2:=segment_000000_hPm1_2 pmStore
  have hP1_3:pmFinal 5003=(bw_matmul (pmFinal 1003) (pmFinal 2003) (pmFinal 3003)).2:=segment_000000_hPm1_3 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP1_0
  simp only [bw_matmul,batchedMatmulBwd] at hP1_1
  simp only [bw_matmul,batchedMatmulBwd] at hP1_2
  simp only [bw_matmul,batchedMatmulBwd] at hP1_3
  have hC1:=TrainVerify.Denote.bw_matmul_snd_head_gather_rank4 4 1 1 16 16 16 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV1:smFinal 401=allGatherPrimDimN 1 4 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003]:=by
    rw [hS1,hgV,hxV,hyV,hC1]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP1_0, ←hP1_1, ←hP1_2, ←hP1_3]
  have hFull1:(smFinal 401).shape=[1, 4, 16, 16]:=by rw [hS1];exact fw_matmul_rank4_shape _ _ 1 4 16 16 16 (segment_000000_transpose_shape _ 1 4 16 16 hx.full_shape) hg.full_shape
  have hout1:fact_out1.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 401) [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] 1 [1, 4, 16, 16] [1, 1, 16, 16]
    refine {full_value:=hV1,full_shape:=hFull1,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1 | hh2 | hh3
      · subst piece;rw [hP1_0];exact fw_matmul_rank4_shape _ _ 1 1 16 16 16 (segment_000000_transpose_shape _ 1 1 16 16 (hx.shard_shapes (pmFinal 2000) (by simp))) (hg.shard_shapes (pmFinal 1000) (by simp))
      · subst piece;rw [hP1_1];exact fw_matmul_rank4_shape _ _ 1 1 16 16 16 (segment_000000_transpose_shape _ 1 1 16 16 (hx.shard_shapes (pmFinal 2001) (by simp))) (hg.shard_shapes (pmFinal 1001) (by simp))
      · subst piece;rw [hP1_2];exact fw_matmul_rank4_shape _ _ 1 1 16 16 16 (segment_000000_transpose_shape _ 1 1 16 16 (hx.shard_shapes (pmFinal 2002) (by simp))) (hg.shard_shapes (pmFinal 1002) (by simp))
      · subst piece;rw [hP1_3];exact fw_matmul_rank4_shape _ _ 1 1 16 16 16 (segment_000000_transpose_shape _ 1 1 16 16 (hx.shard_shapes (pmFinal 2003) (by simp))) (hg.shard_shapes (pmFinal 1003) (by simp))
    · simp only [List.length_cons,List.length_nil];native_decide
  intro fact hfact
  have hc:fact∈[fact_out0, fact_out1]++state_000000.facts:=(show state_000001.facts⊆[fact_out0, fact_out1]++state_000000.facts by native_decide) hfact
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with (rfl | rfl) | old
  · exact hout0
  · exact hout1
  · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate MatmulHeadCase2.smGraph MatmulHeadCase2.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore h;have hh:=segment_000000_sound smStore pmStore h;unfold segment_000000_sm_final segment_000000_pm_final at hh;exact hh

#print axioms segment_000000
end
end MatmulHeadCase2
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulHeadCase3
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003, 1004] 1 [2, 10, 5, 11] [2, 2, 5, 11]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003, 2004] 1 [2, 10, 5, 7] [2, 2, 5, 7]
def fact_y : RelationFact := .sharded 300 [3000, 3001, 3002, 3003, 3004] 1 [2, 10, 7, 11] [2, 2, 7, 11]
def fact_out0 : RelationFact := .sharded 400 [4000, 4001, 4002, 4003, 4004] 1 [2, 10, 5, 7] [2, 2, 5, 7]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_out0]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] }]
@[irreducible] private def segment_000000_sm_final(s:Store):Store:=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) s
@[irreducible] private def segment_000000_pm_final(s:Store):Store:=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) s
private theorem segment_000000_hSm0(smStore:Store):(segment_000000_sm_final smStore) 400=(bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase3.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_0(pmStore:Store):(segment_000000_pm_final pmStore) 4000=(bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase3.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_1(pmStore:Store):(segment_000000_pm_final pmStore) 4001=(bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3001)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } 4001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3001)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase3.pmGraph t 1 1001 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3001)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_2(pmStore:Store):(segment_000000_pm_final pmStore) 4002=(bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3002)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } 4002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3002)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase3.pmGraph t 2 1002 2002 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3002)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_3(pmStore:Store):(segment_000000_pm_final pmStore) 4003=(bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4003 = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3003)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } 4003
      (fun t => (bw_matmul (t 1003) (t 2003) (t 3003)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase3.pmGraph t 3 1003 2003 3003 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3003 = (segment_000000_pm_final pmStore) 3003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3003)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm0_4(pmStore:Store):(segment_000000_pm_final pmStore) 4004=(bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3004)).1:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4004 = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3004)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] } 4004
      (fun t => (bw_matmul (t 1004) (t 2004) (t 3004)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulHeadCase3.pmGraph t 4 1004 2004 3004 4004 5004 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1004 = (segment_000000_pm_final pmStore) 1004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 1004
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2004 = (segment_000000_pm_final pmStore) 2004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 2004
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3004 = (segment_000000_pm_final pmStore) 3004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 3004
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4004 = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3004)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase3.pmGraph) pmStore 3004)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3004)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_transpose_shape (t:Tensor)(a b c d:Nat)(ht:t.shape=[a,b,c,d]):(transpose2d t).shape=[a,b,d,c]:=by
  simp only [transpose2d,ht,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,Tensor.mkShape]
set_option maxHeartbeats 500000 in
private theorem segment_000000_sound(smStore pmStore:Store)(hstate:state_000000.Holds smStore pmStore):state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore):=by
  let smFinal:=segment_000000_sm_final smStore
  let pmFinal:=segment_000000_pm_final pmStore
  have hframe:state_000000.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final;apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg:fact_g.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] 1 [2, 10, 5, 11] [2, 2, 5, 11] at hg
  have hgV:smFinal 100=allGatherPrimDimN 1 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004]:=by simpa only [List.length_cons,List.length_nil] using hg.full_value
  have hx:fact_x.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] 1 [2, 10, 5, 7] [2, 2, 5, 7] at hx
  have hxV:smFinal 200=allGatherPrimDimN 1 5 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
  have hy:fact_y.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004] 1 [2, 10, 7, 11] [2, 2, 7, 11] at hy
  have hyV:smFinal 300=allGatherPrimDimN 1 5 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004]:=by simpa only [List.length_cons,List.length_nil] using hy.full_value
  have hS0:smFinal 400=(bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).1:=segment_000000_hSm0 smStore
  have hP0_0:pmFinal 4000=(bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1:=segment_000000_hPm0_0 pmStore
  have hP0_1:pmFinal 4001=(bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3001)).1:=segment_000000_hPm0_1 pmStore
  have hP0_2:pmFinal 4002=(bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3002)).1:=segment_000000_hPm0_2 pmStore
  have hP0_3:pmFinal 4003=(bw_matmul (pmFinal 1003) (pmFinal 2003) (pmFinal 3003)).1:=segment_000000_hPm0_3 pmStore
  have hP0_4:pmFinal 4004=(bw_matmul (pmFinal 1004) (pmFinal 2004) (pmFinal 3004)).1:=segment_000000_hPm0_4 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP0_0
  simp only [bw_matmul,batchedMatmulBwd] at hP0_1
  simp only [bw_matmul,batchedMatmulBwd] at hP0_2
  simp only [bw_matmul,batchedMatmulBwd] at hP0_3
  simp only [bw_matmul,batchedMatmulBwd] at hP0_4
  have hC0:=TrainVerify.Denote.bw_matmul_fst_head_gather_rank4 5 2 2 5 7 11 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV0:smFinal 400=allGatherPrimDimN 1 5 0 [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003, pmFinal 4004]:=by
    rw [hS0,hgV,hxV,hyV,hC0]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP0_0, ←hP0_1, ←hP0_2, ←hP0_3, ←hP0_4]
  have hFull0:(smFinal 400).shape=[2, 10, 5, 7]:=by rw [hS0];exact fw_matmul_rank4_shape _ _ 2 10 5 11 7 hg.full_shape (segment_000000_transpose_shape _ 2 10 7 11 hy.full_shape)
  have hout0:fact_out0.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003, pmFinal 4004] 1 [2, 10, 5, 7] [2, 2, 5, 7]
    refine {full_value:=hV0,full_shape:=hFull0,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1 | hh2 | hh3 | hh4
      · subst piece;rw [hP0_0];exact fw_matmul_rank4_shape _ _ 2 2 5 11 7 (hg.shard_shapes (pmFinal 1000) (by simp)) (segment_000000_transpose_shape _ 2 2 7 11 (hy.shard_shapes (pmFinal 3000) (by simp)))
      · subst piece;rw [hP0_1];exact fw_matmul_rank4_shape _ _ 2 2 5 11 7 (hg.shard_shapes (pmFinal 1001) (by simp)) (segment_000000_transpose_shape _ 2 2 7 11 (hy.shard_shapes (pmFinal 3001) (by simp)))
      · subst piece;rw [hP0_2];exact fw_matmul_rank4_shape _ _ 2 2 5 11 7 (hg.shard_shapes (pmFinal 1002) (by simp)) (segment_000000_transpose_shape _ 2 2 7 11 (hy.shard_shapes (pmFinal 3002) (by simp)))
      · subst piece;rw [hP0_3];exact fw_matmul_rank4_shape _ _ 2 2 5 11 7 (hg.shard_shapes (pmFinal 1003) (by simp)) (segment_000000_transpose_shape _ 2 2 7 11 (hy.shard_shapes (pmFinal 3003) (by simp)))
      · subst piece;rw [hP0_4];exact fw_matmul_rank4_shape _ _ 2 2 5 11 7 (hg.shard_shapes (pmFinal 1004) (by simp)) (segment_000000_transpose_shape _ 2 2 7 11 (hy.shard_shapes (pmFinal 3004) (by simp)))
    · simp only [List.length_cons,List.length_nil];native_decide
  intro fact hfact
  have hc:fact∈[fact_out0]++state_000000.facts:=(show state_000001.facts⊆[fact_out0]++state_000000.facts by native_decide) hfact
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | old
  · exact hout0
  · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate MatmulHeadCase3.smGraph MatmulHeadCase3.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore h;have hh:=segment_000000_sound smStore pmStore h;unfold segment_000000_sm_final segment_000000_pm_final at hh;exact hh

#print axioms segment_000000
end
end MatmulHeadCase3
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulHeadCase4
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003, 1004] 1 [2, 10, 5, 11] [2, 2, 5, 11]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003, 2004] 1 [2, 10, 5, 7] [2, 2, 5, 7]
def fact_y : RelationFact := .sharded 300 [3000, 3001, 3002, 3003, 3004] 1 [2, 10, 7, 11] [2, 2, 7, 11]
def fact_out1 : RelationFact := .sharded 401 [5000, 5001, 5002, 5003, 5004] 1 [2, 10, 7, 11] [2, 2, 7, 11]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_out1]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] }]
@[irreducible] private def segment_000000_sm_final(s:Store):Store:=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) s
@[irreducible] private def segment_000000_pm_final(s:Store):Store:=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) s
private theorem segment_000000_hSm1(smStore:Store):(segment_000000_sm_final smStore) 401=(bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2:=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase4.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_0(pmStore:Store):(segment_000000_pm_final pmStore) 5000=(bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase4.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_1(pmStore:Store):(segment_000000_pm_final pmStore) 5001=(bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3001)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } 5001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3001)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase4.pmGraph t 1 1001 2001 3001 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3001 = (segment_000000_pm_final pmStore) 3001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3001], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3001)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3001)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_2(pmStore:Store):(segment_000000_pm_final pmStore) 5002=(bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3002)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } 5002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3002)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase4.pmGraph t 2 1002 2002 3002 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3002 = (segment_000000_pm_final pmStore) 3002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3002], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3002)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3002)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_3(pmStore:Store):(segment_000000_pm_final pmStore) 5003=(bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5003 = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3003)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } 5003
      (fun t => (bw_matmul (t 1003) (t 2003) (t 3003)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase4.pmGraph t 3 1003 2003 3003 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3003 = (segment_000000_pm_final pmStore) 3003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3003], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3003)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3003)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_hPm1_4(pmStore:Store):(segment_000000_pm_final pmStore) 5004=(bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3004)).2:=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5004 = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3004)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] } 5004
      (fun t => (bw_matmul (t 1004) (t 2004) (t 3004)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulHeadCase4.pmGraph t 4 1004 2004 3004 4004 5004 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1004 = (segment_000000_pm_final pmStore) 1004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 1004
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2004 = (segment_000000_pm_final pmStore) 2004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 2004
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3004 = (segment_000000_pm_final pmStore) 3004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulHeadCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3004], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 3004
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5004 = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3004)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulHeadCase4.pmGraph) pmStore 3004)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3004)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout
private theorem segment_000000_transpose_shape (t:Tensor)(a b c d:Nat)(ht:t.shape=[a,b,c,d]):(transpose2d t).shape=[a,b,d,c]:=by
  simp only [transpose2d,ht,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,Tensor.mkShape]
set_option maxHeartbeats 500000 in
private theorem segment_000000_sound(smStore pmStore:Store)(hstate:state_000000.Holds smStore pmStore):state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore):=by
  let smFinal:=segment_000000_sm_final smStore
  let pmFinal:=segment_000000_pm_final pmStore
  have hframe:state_000000.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final;apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg:fact_g.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] 1 [2, 10, 5, 11] [2, 2, 5, 11] at hg
  have hgV:smFinal 100=allGatherPrimDimN 1 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004]:=by simpa only [List.length_cons,List.length_nil] using hg.full_value
  have hx:fact_x.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] 1 [2, 10, 5, 7] [2, 2, 5, 7] at hx
  have hxV:smFinal 200=allGatherPrimDimN 1 5 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
  have hy:fact_y.Holds smFinal pmFinal:=hframe _ (by native_decide)
  change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004] 1 [2, 10, 7, 11] [2, 2, 7, 11] at hy
  have hyV:smFinal 300=allGatherPrimDimN 1 5 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004]:=by simpa only [List.length_cons,List.length_nil] using hy.full_value
  have hS1:smFinal 401=(bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).2:=segment_000000_hSm1 smStore
  have hP1_0:pmFinal 5000=(bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2:=segment_000000_hPm1_0 pmStore
  have hP1_1:pmFinal 5001=(bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3001)).2:=segment_000000_hPm1_1 pmStore
  have hP1_2:pmFinal 5002=(bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3002)).2:=segment_000000_hPm1_2 pmStore
  have hP1_3:pmFinal 5003=(bw_matmul (pmFinal 1003) (pmFinal 2003) (pmFinal 3003)).2:=segment_000000_hPm1_3 pmStore
  have hP1_4:pmFinal 5004=(bw_matmul (pmFinal 1004) (pmFinal 2004) (pmFinal 3004)).2:=segment_000000_hPm1_4 pmStore
  simp only [bw_matmul,batchedMatmulBwd] at hP1_0
  simp only [bw_matmul,batchedMatmulBwd] at hP1_1
  simp only [bw_matmul,batchedMatmulBwd] at hP1_2
  simp only [bw_matmul,batchedMatmulBwd] at hP1_3
  simp only [bw_matmul,batchedMatmulBwd] at hP1_4
  have hC1:=TrainVerify.Denote.bw_matmul_snd_head_gather_rank4 5 2 2 5 7 11 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] [pmFinal 3000, pmFinal 3001, pmFinal 3002, pmFinal 3003, pmFinal 3004]
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes
  have hV1:smFinal 401=allGatherPrimDimN 1 5 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003, pmFinal 5004]:=by
    rw [hS1,hgV,hxV,hyV,hC1]
    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]
    rw [←hP1_0, ←hP1_1, ←hP1_2, ←hP1_3, ←hP1_4]
  have hFull1:(smFinal 401).shape=[2, 10, 7, 11]:=by rw [hS1];exact fw_matmul_rank4_shape _ _ 2 10 7 5 11 (segment_000000_transpose_shape _ 2 10 5 7 hx.full_shape) hg.full_shape
  have hout1:fact_out1.Holds smFinal pmFinal:=by
    change ShardedRel (smFinal 401) [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003, pmFinal 5004] 1 [2, 10, 7, 11] [2, 2, 7, 11]
    refine {full_value:=hV1,full_shape:=hFull1,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hh0 | hh1 | hh2 | hh3 | hh4
      · subst piece;rw [hP1_0];exact fw_matmul_rank4_shape _ _ 2 2 7 5 11 (segment_000000_transpose_shape _ 2 2 5 7 (hx.shard_shapes (pmFinal 2000) (by simp))) (hg.shard_shapes (pmFinal 1000) (by simp))
      · subst piece;rw [hP1_1];exact fw_matmul_rank4_shape _ _ 2 2 7 5 11 (segment_000000_transpose_shape _ 2 2 5 7 (hx.shard_shapes (pmFinal 2001) (by simp))) (hg.shard_shapes (pmFinal 1001) (by simp))
      · subst piece;rw [hP1_2];exact fw_matmul_rank4_shape _ _ 2 2 7 5 11 (segment_000000_transpose_shape _ 2 2 5 7 (hx.shard_shapes (pmFinal 2002) (by simp))) (hg.shard_shapes (pmFinal 1002) (by simp))
      · subst piece;rw [hP1_3];exact fw_matmul_rank4_shape _ _ 2 2 7 5 11 (segment_000000_transpose_shape _ 2 2 5 7 (hx.shard_shapes (pmFinal 2003) (by simp))) (hg.shard_shapes (pmFinal 1003) (by simp))
      · subst piece;rw [hP1_4];exact fw_matmul_rank4_shape _ _ 2 2 7 5 11 (segment_000000_transpose_shape _ 2 2 5 7 (hx.shard_shapes (pmFinal 2004) (by simp))) (hg.shard_shapes (pmFinal 1004) (by simp))
    · simp only [List.length_cons,List.length_nil];native_decide
  intro fact hfact
  have hc:fact∈[fact_out1]++state_000000.facts:=(show state_000001.facts⊆[fact_out1]++state_000000.facts by native_decide) hfact
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | old
  · exact hout1
  · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate MatmulHeadCase4.smGraph MatmulHeadCase4.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore h;have hh:=segment_000000_sound smStore pmStore h;unfold segment_000000_sm_final segment_000000_pm_final at hh;exact hh

#print axioms segment_000000
end
end MatmulHeadCase4
