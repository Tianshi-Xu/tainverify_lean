import denote.RelationCompiler
import denote.KRankBWLayernorm
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWLayernorm
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_layernorm", ins := [100, 200, 700, 701], outs := [300, 301, 302] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_layernorm", ins := [1000, 2000, 700, 701], outs := [3000, 4000, 5000] }, { rank := 1, op := "OpName.BW_layernorm", ins := [1001, 2001, 700, 701], outs := [3001, 4001, 5001] }, { rank := 2, op := "OpName.BW_layernorm", ins := [1002, 2002, 700, 701], outs := [3002, 4002, 5002] }] }
def fg : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 9, 7] [2, 3, 7]
def fx : RelationFact := .sharded 200 [2000, 2001, 2002] 1 [2, 9, 7] [2, 3, 7]
def fw : RelationFact := .sharded 700 [700] 0 [7] [7]
def fb : RelationFact := .sharded 701 [701] 0 [7] [7]
def fo : RelationFact := .sharded 300 [3000, 3001, 3002] 1 [2, 9, 7] [2, 3, 7]
def before : RelationState where
  facts := [fg, fx, fw, fb]
  nonempty := by decide
def after : RelationState where
  facts := [fg, fx, fw, fb, fo]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_layernorm", ins := [100, 200, 700, 701], outs := [300, 301, 302] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_layernorm", ins := [1000, 2000, 700, 701], outs := [3000, 4000, 5000] }, { rank := 1, op := "OpName.BW_layernorm", ins := [1001, 2001, 700, 701], outs := [3001, 4001, 5001] }, { rank := 2, op := "OpName.BW_layernorm", ins := [1002, 2002, 700, 701], outs := [3002, 4002, 5002] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 300 = (bw_layernorm ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 700) ((segment_000000_sm_final smStore) 701)).1 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_layernorm", ins := [100, 200, 700, 701], outs := [300, 301, 302] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = (bw_layernorm (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 700) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 701)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLayernorm.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_layernorm", ins := [100, 200, 700, 701], outs := [300, 301, 302] } 300
      (fun t => (bw_layernorm (t 100) (t 200) (t 700) (t 701)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_layernorm_dx_out SyntheticBWLayernorm.smGraph t 0 100 200 700 701 300 301 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_layernorm", ins := [100, 200, 700, 701], outs := [300, 301, 302] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_layernorm", ins := [100, 200, 700, 701], outs := [300, 301, 302] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 700 = (segment_000000_sm_final smStore) 700 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_layernorm", ins := [100, 200, 700, 701], outs := [300, 301, 302] } :: (segment_000000_sm_nodes.drop 1)) 700
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 701 = (segment_000000_sm_final smStore) 701 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_layernorm", ins := [100, 200, 700, 701], outs := [300, 301, 302] } :: (segment_000000_sm_nodes.drop 1)) 701
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = (bw_layernorm ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 700) ((segment_000000_sm_final smStore) 701)).1 := by
    calc
      _ = (bw_layernorm (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 700) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.smGraph) smStore 701)).1 := hout_prefix
      _ = (bw_layernorm ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 700) ((segment_000000_sm_final smStore) 701)).1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3000 = (bw_layernorm ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 700) ((segment_000000_pm_final pmStore) 701)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_layernorm", ins := [1000, 2000, 700, 701], outs := [3000, 4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = (bw_layernorm (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 700) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 701)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_layernorm", ins := [1000, 2000, 700, 701], outs := [3000, 4000, 5000] } 3000
      (fun t => (bw_layernorm (t 1000) (t 2000) (t 700) (t 701)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_layernorm_dx_out SyntheticBWLayernorm.pmGraph t 0 1000 2000 700 701 3000 4000 5000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_layernorm", ins := [1000, 2000, 700, 701], outs := [3000, 4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_layernorm", ins := [1000, 2000, 700, 701], outs := [3000, 4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 700 = (segment_000000_pm_final pmStore) 700 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_layernorm", ins := [1000, 2000, 700, 701], outs := [3000, 4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 700
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 701 = (segment_000000_pm_final pmStore) 701 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_layernorm", ins := [1000, 2000, 700, 701], outs := [3000, 4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 701
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = (bw_layernorm ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 700) ((segment_000000_pm_final pmStore) 701)).1 := by
    calc
      _ = (bw_layernorm (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 700) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 701)).1 := hout_prefix
      _ = (bw_layernorm ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 700) ((segment_000000_pm_final pmStore) 701)).1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3001 = (bw_layernorm ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 700) ((segment_000000_pm_final pmStore) 701)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_layernorm", ins := [1001, 2001, 700, 701], outs := [3001, 4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3001 = (bw_layernorm (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 700) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 701)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_layernorm", ins := [1001, 2001, 700, 701], outs := [3001, 4001, 5001] } 3001
      (fun t => (bw_layernorm (t 1001) (t 2001) (t 700) (t 701)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_layernorm_dx_out SyntheticBWLayernorm.pmGraph t 1 1001 2001 700 701 3001 4001 5001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_layernorm", ins := [1001, 2001, 700, 701], outs := [3001, 4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_layernorm", ins := [1001, 2001, 700, 701], outs := [3001, 4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 700 = (segment_000000_pm_final pmStore) 700 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_layernorm", ins := [1001, 2001, 700, 701], outs := [3001, 4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 700
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 701 = (segment_000000_pm_final pmStore) 701 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_layernorm", ins := [1001, 2001, 700, 701], outs := [3001, 4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 701
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3001 = (bw_layernorm ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 700) ((segment_000000_pm_final pmStore) 701)).1 := by
    calc
      _ = (bw_layernorm (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 700) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 701)).1 := hout_prefix
      _ = (bw_layernorm ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 700) ((segment_000000_pm_final pmStore) 701)).1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3002 = (bw_layernorm ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 700) ((segment_000000_pm_final pmStore) 701)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_layernorm", ins := [1002, 2002, 700, 701], outs := [3002, 4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3002 = (bw_layernorm (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 700) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 701)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_layernorm", ins := [1002, 2002, 700, 701], outs := [3002, 4002, 5002] } 3002
      (fun t => (bw_layernorm (t 1002) (t 2002) (t 700) (t 701)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_layernorm_dx_out SyntheticBWLayernorm.pmGraph t 2 1002 2002 700 701 3002 4002 5002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_layernorm", ins := [1002, 2002, 700, 701], outs := [3002, 4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_layernorm", ins := [1002, 2002, 700, 701], outs := [3002, 4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 700 = (segment_000000_pm_final pmStore) 700 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_layernorm", ins := [1002, 2002, 700, 701], outs := [3002, 4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 700
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 701 = (segment_000000_pm_final pmStore) 701 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWLayernorm.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_layernorm", ins := [1002, 2002, 700, 701], outs := [3002, 4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 701
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3002 = (bw_layernorm ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 700) ((segment_000000_pm_final pmStore) 701)).1 := by
    calc
      _ = (bw_layernorm (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 700) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWLayernorm.pmGraph) pmStore 701)).1 := hout_prefix
      _ = (bw_layernorm ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 700) ((segment_000000_pm_final pmStore) 701)).1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_dx_shape (g x w b : Tensor) (s : Nat)
    (hx : x.shape = [2, s, 7]) :
    (bw_layernorm g x w b).1.shape = [2, s, 7] := by
  calc
    (bw_layernorm g x w b).1.shape = x.shape :=
      bw_layernorm_dx_shape g x w b 7 [s, 2] (by rw [hx]; rfl)
    _ = [2, s, 7] := hx

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : before.Holds smStore pmStore) :
    after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
    let smFinal := segment_000000_sm_final smStore
    let pmFinal := segment_000000_pm_final pmStore
    have hframe : before.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 1 [2, 9, 7] [2, 3, 7] at hg
    have hx : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 1 [2, 9, 7] [2, 3, 7] at hx
    have hgamma : fw.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 700) [pmFinal 700] 0 [7] [7] at hgamma
    have hGammaValue : smFinal 700 = pmFinal 700 := by
      rw [hgamma.full_value]
      simpa only [List.length_cons, List.length_nil] using
        (allGatherPrimDimN_singleton_eq 0 (pmFinal 700) (by
          rw [hgamma.shard_shapes (pmFinal 700) (by simp)]; decide))
    have hbeta : fb.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 701) [pmFinal 701] 0 [7] [7] at hbeta
    have hBetaValue : smFinal 701 = pmFinal 701 := by
      rw [hbeta.full_value]
      simpa only [List.length_cons, List.length_nil] using
        (allGatherPrimDimN_singleton_eq 0 (pmFinal 701) (by
          rw [hbeta.shard_shapes (pmFinal 701) (by simp)]; decide))
    have hgValue : smFinal 100 = allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hxValue : smFinal 200 = allGatherPrimDimN 1 3 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 300 =
        (bw_layernorm (smFinal 100) (smFinal 200)
          (smFinal 700) (smFinal 701)).1 :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 3000 =
        (bw_layernorm (pmFinal 1000) (pmFinal 2000)
          (pmFinal 700) (pmFinal 701)).1 :=
      segment_000000_hPmWriter0 pmStore
    have hgShape0 := hg.shard_shapes (pmFinal 1000) (by simp)
    have hxShape0 := hx.shard_shapes (pmFinal 2000) (by simp)
    have hOutShape0 : (pmFinal 3000).shape = [2, 3, 7] := by
      rw [hPmWriter0]
      exact segment_000000_dx_shape _ _ _ _ 3 hxShape0
    have hPmWriter1 : pmFinal 3001 =
        (bw_layernorm (pmFinal 1001) (pmFinal 2001)
          (pmFinal 700) (pmFinal 701)).1 :=
      segment_000000_hPmWriter1 pmStore
    have hgShape1 := hg.shard_shapes (pmFinal 1001) (by simp)
    have hxShape1 := hx.shard_shapes (pmFinal 2001) (by simp)
    have hOutShape1 : (pmFinal 3001).shape = [2, 3, 7] := by
      rw [hPmWriter1]
      exact segment_000000_dx_shape _ _ _ _ 3 hxShape1
    have hPmWriter2 : pmFinal 3002 =
        (bw_layernorm (pmFinal 1002) (pmFinal 2002)
          (pmFinal 700) (pmFinal 701)).1 :=
      segment_000000_hPmWriter2 pmStore
    have hgShape2 := hg.shard_shapes (pmFinal 1002) (by simp)
    have hxShape2 := hx.shard_shapes (pmFinal 2002) (by simp)
    have hOutShape2 : (pmFinal 3002).shape = [2, 3, 7] := by
      rw [hPmWriter2]
      exact segment_000000_dx_shape _ _ _ _ 3 hxShape2
    have hcomm := TrainVerify.Denote.bw_layernorm_dx_allGatherPrimDimN_dim1_3d 3 2 3 7
      [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] (pmFinal 700) (pmFinal 701)
      (by decide) (by decide) (by decide) (by decide) (by simp) (by simp)
      (by simp [hgShape0, hgShape1, hgShape2])
      (by simp [hxShape0, hxShape1, hxShape2])
    have hOutValue : smFinal 300 = allGatherPrimDimN 1 3 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002] := by
      rw [hSmWriter, hgValue, hxValue, hGammaValue, hBetaValue, hcomm]
      simp only [List.zipWith]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
    have hOutValueList : smFinal 300 =
        allGatherPrimDimN 1 [pmFinal 3000, pmFinal 3001, pmFinal 3002].length 0 [pmFinal 3000, pmFinal 3001, pmFinal 3002] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 300).shape = [2, 9, 7] := by
      rw [hSmWriter]
      exact segment_000000_dx_shape _ _ _ _ 9 hx.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 3000, pmFinal 3001, pmFinal 3002] 1 [2, 9, 7] [2, 3, 7]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := by decide
        shard_shapes := ?_
        shape_contract := ?_
      }
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst shard
          exact hOutShape0
        · subst shard
          exact hOutShape1
        · subst shard
          exact hOutShape2
      · simp only [List.length_cons, List.length_nil]
        native_decide
    intro fact hfact
    have covered : fact ∈ [fo] ++ before.facts := by
      exact (show after.facts ⊆ [fo] ++ before.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticBWLayernorm.smGraph SyntheticBWLayernorm.pmGraph before after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end SyntheticBWLayernorm
