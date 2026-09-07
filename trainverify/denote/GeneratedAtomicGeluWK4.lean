/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace SyntheticBWGeluWred

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_gelu", ins := [10, 20], outs := [30] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_gelu", ins := [100, 200], outs := [300] }, { rank := 1, op := "OpName.BW_gelu", ins := [101, 201], outs := [301] }, { rank := 2, op := "OpName.BW_gelu", ins := [102, 202], outs := [302] }, { rank := 0, op := "OpName.CROSS_DP_WRED", ins := [600, 601, 602, 603], outs := [600] }, { rank := 3, op := "OpName.BW_gelu", ins := [103, 203], outs := [303] }] }


private def fg : RelationFact :=
  .sharded 10 [100, 101, 102, 103] 1 [2, 12] [2, 3]

private def fx : RelationFact :=
  .sharded 20 [200, 201, 202, 203] 1 [2, 12] [2, 3]

private def fo : RelationFact :=
  .sharded 30 [300, 301, 302, 303] 1 [2, 12] [2, 3]

private def fw : RelationFact :=
  .reduction 50 [600, 601, 602, 603] [5, 7]

private def fj : RelationFact :=
  .joined 50 600 [5, 7]

private def anchor : RelationFact :=
  .tensorShape .sm 99 [1]

private def state_000000 : RelationState where
  facts := [anchor, fg, fx, fw]
  nonempty := by decide

private def state_000001 : RelationState where
  facts := [anchor, fg, fx, fo, fj]
  nonempty := by decide

set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_gelu", ins := [10, 20], outs := [30] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_gelu", ins := [100, 200], outs := [300] }, { rank := 1, op := "OpName.BW_gelu", ins := [101, 201], outs := [301] }, { rank := 2, op := "OpName.BW_gelu", ins := [102, 202], outs := [302] }, { rank := 0, op := "OpName.CROSS_DP_WRED", ins := [600, 601, 602, 603], outs := [600] }, { rank := 3, op := "OpName.BW_gelu", ins := [103, 203], outs := [303] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) store
private def segment_000000_frameable : RelationState where
  facts := [anchor, fg, fx]
  nonempty := by native_decide

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 30 = bw_gelu ((segment_000000_sm_final smStore) 10) ((segment_000000_sm_final smStore) 20) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_gelu", ins := [10, 20], outs := [30] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 30 = bw_gelu (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.smGraph) smStore 10) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.smGraph) smStore 20) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWGeluWred.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_gelu", ins := [10, 20], outs := [30] } 30
      (fun t => bw_gelu (t 10) (t 20)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_gelu_out SyntheticBWGeluWred.smGraph t 0 10 20 30
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.smGraph) smStore 10 = (segment_000000_sm_final smStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_gelu", ins := [10, 20], outs := [30] } :: (segment_000000_sm_nodes.drop 1)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.smGraph) smStore 20 = (segment_000000_sm_final smStore) 20 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_gelu", ins := [10, 20], outs := [30] } :: (segment_000000_sm_nodes.drop 1)) 20
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 30 = bw_gelu ((segment_000000_sm_final smStore) 10) ((segment_000000_sm_final smStore) 20) := by
    calc
      _ = bw_gelu (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.smGraph) smStore 10) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.smGraph) smStore 20) := hout_prefix
      _ = bw_gelu ((segment_000000_sm_final smStore) 10) ((segment_000000_sm_final smStore) 20) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_gelu ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_gelu", ins := [100, 200], outs := [300] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_gelu (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_gelu", ins := [100, 200], outs := [300] } 300
      (fun t => bw_gelu (t 100) (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_gelu_out SyntheticBWGeluWred.pmGraph t 0 100 200 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_gelu", ins := [100, 200], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 200 = (segment_000000_pm_final pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_gelu", ins := [100, 200], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_gelu ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) := by
    calc
      _ = bw_gelu (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 200) := hout_prefix
      _ = bw_gelu ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 301 = bw_gelu ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_gelu", ins := [101, 201], outs := [301] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 301 = bw_gelu (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 201) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_gelu", ins := [101, 201], outs := [301] } 301
      (fun t => bw_gelu (t 101) (t 201)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_gelu_out SyntheticBWGeluWred.pmGraph t 1 101 201 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_gelu", ins := [101, 201], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 101
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 201 = (segment_000000_pm_final pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_gelu", ins := [101, 201], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 201
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 301 = bw_gelu ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) := by
    calc
      _ = bw_gelu (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 201) := hout_prefix
      _ = bw_gelu ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 302 = bw_gelu ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_gelu", ins := [102, 202], outs := [302] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 302 = bw_gelu (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 102) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 202) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_gelu", ins := [102, 202], outs := [302] } 302
      (fun t => bw_gelu (t 102) (t 202)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_gelu_out SyntheticBWGeluWred.pmGraph t 2 102 202 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_gelu", ins := [102, 202], outs := [302] } :: (segment_000000_pm_nodes.drop 3)) 102
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 202 = (segment_000000_pm_final pmStore) 202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_gelu", ins := [102, 202], outs := [302] } :: (segment_000000_pm_nodes.drop 3)) 202
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 302 = bw_gelu ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) := by
    calc
      _ = bw_gelu (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 102) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 202) := hout_prefix
      _ = bw_gelu ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 303 = bw_gelu ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 203) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 3, op := "OpName.BW_gelu", ins := [103, 203], outs := [303] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 303 = bw_gelu (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 103) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 203) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 3, op := "OpName.BW_gelu", ins := [103, 203], outs := [303] } 303
      (fun t => bw_gelu (t 103) (t 203)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_gelu_out SyntheticBWGeluWred.pmGraph t 3 103 203 303
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_gelu", ins := [103, 203], outs := [303] } :: (segment_000000_pm_nodes.drop 5)) 103
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 203 = (segment_000000_pm_final pmStore) 203 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWGeluWred.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 3, op := "OpName.BW_gelu", ins := [103, 203], outs := [303] } :: (segment_000000_pm_nodes.drop 5)) 203
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 303 = bw_gelu ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 203) := by
    calc
      _ = bw_gelu (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 103) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore 203) := hout_prefix
      _ = bw_gelu ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 203) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_wred_writer_0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 600 = cross_dp_wred ([600, 601, 602, 603].map pmStore) := by
  have hfinal : segment_000000_pm_final pmStore = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 0, op := "OpName.CROSS_DP_WRED", ins := [600, 601, 602, 603], outs := [600] }] ++ (segment_000000_pm_nodes.drop 4) := by native_decide
  have hprefix : (segment_000000_pm_final pmStore) 600 =
      cross_dp_wred ([600, 601, 602, 603].map ((segment_000000_pm_nodes.take 3).foldl
        (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore)) := by
    rw [hfinal, hnodes]
    exact foldl_faithful_middle_writer SyntheticBWGeluWred.pmGraph pmStore (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 0, op := "OpName.CROSS_DP_WRED", ins := [600, 601, 602, 603], outs := [600] } 600
      (fun t => cross_dp_wred ([600, 601, 602, 603].map t)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide)
          (hattn := by native_decide)]
        unfold applyNodeDistributed
        rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
        · exact applyNode_cross_dp_wred_out SyntheticBWGeluWred.pmGraph t 0 [600, 601, 602, 603] 600
        · native_decide
        · native_decide
      ) (by native_decide) (by native_decide)
  have hread0 : ((segment_000000_pm_nodes.take 3).foldl
      (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore) 600 = pmStore 600 :=
    foldl_applyNodeDistributedFaithful_at_not_written SyntheticBWGeluWred.pmGraph
      (segment_000000_pm_nodes.take 3) pmStore 600 (by native_decide) (by native_decide)
  have hread1 : ((segment_000000_pm_nodes.take 3).foldl
      (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore) 601 = pmStore 601 :=
    foldl_applyNodeDistributedFaithful_at_not_written SyntheticBWGeluWred.pmGraph
      (segment_000000_pm_nodes.take 3) pmStore 601 (by native_decide) (by native_decide)
  have hread2 : ((segment_000000_pm_nodes.take 3).foldl
      (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore) 602 = pmStore 602 :=
    foldl_applyNodeDistributedFaithful_at_not_written SyntheticBWGeluWred.pmGraph
      (segment_000000_pm_nodes.take 3) pmStore 602 (by native_decide) (by native_decide)
  have hread3 : ((segment_000000_pm_nodes.take 3).foldl
      (applyNodeDistributedFaithful SyntheticBWGeluWred.pmGraph) pmStore) 603 = pmStore 603 :=
    foldl_applyNodeDistributedFaithful_at_not_written SyntheticBWGeluWred.pmGraph
      (segment_000000_pm_nodes.take 3) pmStore 603 (by native_decide) (by native_decide)
  simp only [List.map] at hprefix ⊢
  rw [hread0, hread1, hread2, hread3] at hprefix
  exact hprefix

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
    let smFinal := segment_000000_sm_final smStore
    let pmFinal := segment_000000_pm_final pmStore
    have hFrameInitial : segment_000000_frameable.Holds smStore pmStore := by
      intro fact hfact
      exact hstate fact ((show segment_000000_frameable.facts ⊆ state_000000.facts by native_decide) hfact)
    have hframe : segment_000000_frameable.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hFrameInitial
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 10) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] 1 [2, 12] [2, 3] at hg
    have hx : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 20) [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] 1 [2, 12] [2, 3] at hx
    have hgValue : smFinal 10 = allGatherPrimDimN 1 4 0 [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hxValue : smFinal 20 = allGatherPrimDimN 1 4 0 [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 30 = bw_gelu (smFinal 10) (smFinal 20) :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 300 = bw_gelu (pmFinal 100) (pmFinal 200) :=
      segment_000000_hPmWriter0 pmStore
    have hOutShape0 : (pmFinal 300).shape = [2, 3] := by
      rw [hPmWriter0, bw_gelu_shape]
      exact hx.shard_shapes _ (by simp)
    have hPmWriter1 : pmFinal 301 = bw_gelu (pmFinal 101) (pmFinal 201) :=
      segment_000000_hPmWriter1 pmStore
    have hOutShape1 : (pmFinal 301).shape = [2, 3] := by
      rw [hPmWriter1, bw_gelu_shape]
      exact hx.shard_shapes _ (by simp)
    have hPmWriter2 : pmFinal 302 = bw_gelu (pmFinal 102) (pmFinal 202) :=
      segment_000000_hPmWriter2 pmStore
    have hOutShape2 : (pmFinal 302).shape = [2, 3] := by
      rw [hPmWriter2, bw_gelu_shape]
      exact hx.shard_shapes _ (by simp)
    have hPmWriter3 : pmFinal 303 = bw_gelu (pmFinal 103) (pmFinal 203) :=
      segment_000000_hPmWriter3 pmStore
    have hOutShape3 : (pmFinal 303).shape = [2, 3] := by
      rw [hPmWriter3, bw_gelu_shape]
      exact hx.shard_shapes _ (by simp)
    have hcomm := TrainVerify.Denote.bw_gelu_allGatherPrimDimN_eq 1 4 [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] [2, 3]
      (by omega) (by simp) (by simp)
      (by simpa using hg.shard_shapes _ (by simp))
      (by simpa using hx.shard_shapes _ (by simp))
      (by intro i hi; exact hg.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))
      (by intro i hi; exact hx.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))
    have hOutValue : smFinal 30 = allGatherPrimDimN 1 4 0 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] := by
      rw [hSmWriter, hgValue, hxValue, hcomm]
      simp only [List.zipWith]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2, ← hPmWriter3]
    have hOutValueList : smFinal 30 = allGatherPrimDimN 1 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303].length 0 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 30).shape = [2, 12] := by
      rw [hSmWriter, bw_gelu_shape]
      exact hx.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 30) [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] 1 [2, 12] [2, 3]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := hx.gather_dim_lt
        shard_shapes := ?_
        shape_contract := by
          simp only [List.length_cons, List.length_nil]
          native_decide
      }
      intro piece hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2 | h3
      · subst piece
        exact hOutShape0
      · subst piece
        exact hOutShape1
      · subst piece
        exact hOutShape2
      · subst piece
        exact hOutShape3
    have hinWred0 : fw.Holds smStore pmStore :=
      hstate fw (by native_decide)
    change ReductionRel (smStore 50) ([600, 601, 602, 603].map pmStore) [5, 7] at hinWred0
    have hWredWriter0 := segment_000000_wred_writer_0 pmStore
    change pmFinal 600 = cross_dp_wred ([600, 601, 602, 603].map pmStore) at hWredWriter0
    have hWredReduce0 : pmFinal 600 =
        allReducePrim ([600, 601, 602, 603].map pmStore).length 0 ([600, 601, 602, 603].map pmStore) := by
      rw [hWredWriter0]
      exact cross_dp_wred_eq_allReducePrim _ (by simp)
    have hSmRead0 : smFinal 50 = smStore 50 := by
      unfold smFinal segment_000000_sm_final
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticBWGeluWred.smGraph
        segment_000000_sm_nodes smStore 50 (by native_decide) (by native_decide)
    have hJoined0 : smFinal 50 = pmFinal 600 := by
      rw [hSmRead0]
      exact hinWred0.full_value.trans hWredReduce0.symm
    have houtWred0 : fj.Holds smFinal pmFinal := by
      change smFinal 50 = pmFinal 600 ∧ _ ∧ _
      refine ⟨hJoined0, ?_, ?_⟩
      · rw [hSmRead0]
        exact hinWred0.full_shape
      · rw [← hJoined0, hSmRead0]
        exact hinWred0.full_shape
    intro fact hfact
    have covered : fact ∈ [fo, fj] ++ segment_000000_frameable.facts := by
      exact (show state_000001.facts ⊆ [fo, fj] ++ segment_000000_frameable.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · exact hout
      · exact houtWred0
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticBWGeluWred.smGraph SyntheticBWGeluWred.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000
end
end SyntheticBWGeluWred
