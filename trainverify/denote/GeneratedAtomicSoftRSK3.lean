import denote.KRankBWSoftmaxGeneral
/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace SyntheticBWSoftmaxReduceScatter

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_softmax", ins := [10, 20], outs := [30], params := [3] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }, { rank := 1, op := "OpName.BW_softmax", ins := [101, 201], outs := [301], params := [3] }, { rank := 0, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [700], params := [2] }, { rank := 1, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [701], params := [2] }, { rank := 2, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [702], params := [2] }, { rank := 2, op := "OpName.BW_softmax", ins := [102, 202], outs := [302], params := [3] }] }


private def fg : RelationFact :=
  .sharded 10 [100, 101, 102] 2 [2, 3, 15, 7] [2, 3, 5, 7]

private def fx : RelationFact :=
  .sharded 20 [200, 201, 202] 2 [2, 3, 15, 7] [2, 3, 5, 7]

private def fo : RelationFact :=
  .sharded 30 [300, 301, 302] 2 [2, 3, 15, 7] [2, 3, 5, 7]

private def fw : RelationFact :=
  .reduction 50 [600, 601, 602] [2, 3, 15, 7]

private def fj : RelationFact :=
  .sharded 50 [700, 701, 702] 2 [2, 3, 15, 7] [2, 3, 5, 7]

private def active : RelationFact :=
  .tensorEq .sm 98 .pm 98

private def anchor : RelationFact :=
  .tensorShape .sm 99 [1]

private def state_000000 : RelationState where
  facts := [anchor, active, fg, fx, fw]
  nonempty := by decide

private def state_000001 : RelationState where
  facts := [anchor, active, fg, fx, fo, fj]
  nonempty := by decide

set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_softmax", ins := [10, 20], outs := [30], params := [3] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }, { rank := 1, op := "OpName.BW_softmax", ins := [101, 201], outs := [301], params := [3] }, { rank := 0, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [700], params := [2] }, { rank := 1, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [701], params := [2] }, { rank := 2, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [702], params := [2] }, { rank := 2, op := "OpName.BW_softmax", ins := [102, 202], outs := [302], params := [3] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 30 = bw_softmax ((segment_000000_sm_final smStore) 10) ((segment_000000_sm_final smStore) 20) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [10, 20], outs := [30], params := [3] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 30 = bw_softmax (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.smGraph) smStore 10) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.smGraph) smStore 20) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWSoftmaxReduceScatter.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_softmax", ins := [10, 20], outs := [30], params := [3] } 30
      (fun t => bw_softmax (t 10) (t 20)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 SyntheticBWSoftmaxReduceScatter.smGraph t 0 10 20 30 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.smGraph) smStore 10 = (segment_000000_sm_final smStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_softmax", ins := [10, 20], outs := [30], params := [3] } :: (segment_000000_sm_nodes.drop 1)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.smGraph) smStore 20 = (segment_000000_sm_final smStore) 20 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_softmax", ins := [10, 20], outs := [30], params := [3] } :: (segment_000000_sm_nodes.drop 1)) 20
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 30 = bw_softmax ((segment_000000_sm_final smStore) 10) ((segment_000000_sm_final smStore) 20) := by
    calc
      _ = bw_softmax (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.smGraph) smStore 10) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.smGraph) smStore 20) := hout_prefix
      _ = bw_softmax ((segment_000000_sm_final smStore) 10) ((segment_000000_sm_final smStore) 20) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_softmax ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_softmax (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } 300
      (fun t => bw_softmax (t 100) (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 SyntheticBWSoftmaxReduceScatter.pmGraph t 0 100 200 300 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 200 = (segment_000000_pm_final pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_softmax", ins := [100, 200], outs := [300], params := [3] } :: (segment_000000_pm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_softmax ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 200) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 301 = bw_softmax ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_softmax", ins := [101, 201], outs := [301], params := [3] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 301 = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 201) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_softmax", ins := [101, 201], outs := [301], params := [3] } 301
      (fun t => bw_softmax (t 101) (t 201)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 SyntheticBWSoftmaxReduceScatter.pmGraph t 1 101 201 301 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_softmax", ins := [101, 201], outs := [301], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 101
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 201 = (segment_000000_pm_final pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_softmax", ins := [101, 201], outs := [301], params := [3] } :: (segment_000000_pm_nodes.drop 2)) 201
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 301 = bw_softmax ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 201) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 302 = bw_softmax ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_softmax", ins := [102, 202], outs := [302], params := [3] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 302 = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 102) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 202) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_softmax", ins := [102, 202], outs := [302], params := [3] } 302
      (fun t => bw_softmax (t 102) (t 202)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_softmax_out_g234 SyntheticBWSoftmaxReduceScatter.pmGraph t 2 102 202 302 [3]
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [102, 202], outs := [302], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 102
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 202 = (segment_000000_pm_final pmStore) 202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_softmax", ins := [102, 202], outs := [302], params := [3] } :: (segment_000000_pm_nodes.drop 6)) 202
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 302 = bw_softmax ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) := by
    calc
      _ = bw_softmax (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 102) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 202) := hout_prefix
      _ = bw_softmax ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_scatter_writer0 (pmStore : Store) : (segment_000000_pm_final pmStore) 700 = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 0 [(segment_000000_pm_final pmStore) 600, (segment_000000_pm_final pmStore) 601, (segment_000000_pm_final pmStore) 602] := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 0, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [700], params := [2] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 700 = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 0 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 600, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 601, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 602] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 0, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [700], params := [2] } 700
      (fun t => reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 0 [t 600, t 601, t 602]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_reduceScatterPrim_out SyntheticBWSoftmaxReduceScatter.pmGraph t 0 2 [600, 601, 602] 700
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 600 = (segment_000000_pm_final pmStore) 600 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [700], params := [2] } :: (segment_000000_pm_nodes.drop 3)) 600
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 601 = (segment_000000_pm_final pmStore) 601 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [700], params := [2] } :: (segment_000000_pm_nodes.drop 3)) 601
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 602 = (segment_000000_pm_final pmStore) 602 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [700], params := [2] } :: (segment_000000_pm_nodes.drop 3)) 602
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 700 = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 0 [(segment_000000_pm_final pmStore) 600, (segment_000000_pm_final pmStore) 601, (segment_000000_pm_final pmStore) 602] := by
    calc
      _ = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 0 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 600, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 601, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 602] := hout_prefix
      _ = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 0 [(segment_000000_pm_final pmStore) 600, (segment_000000_pm_final pmStore) 601, (segment_000000_pm_final pmStore) 602] := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_scatter_writer1 (pmStore : Store) : (segment_000000_pm_final pmStore) 701 = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 1 [(segment_000000_pm_final pmStore) 600, (segment_000000_pm_final pmStore) 601, (segment_000000_pm_final pmStore) 602] := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [701], params := [2] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 701 = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 1 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 600, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 601, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 602] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [701], params := [2] } 701
      (fun t => reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 1 [t 600, t 601, t 602]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_reduceScatterPrim_out SyntheticBWSoftmaxReduceScatter.pmGraph t 1 2 [600, 601, 602] 701
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 600 = (segment_000000_pm_final pmStore) 600 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [701], params := [2] } :: (segment_000000_pm_nodes.drop 4)) 600
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 601 = (segment_000000_pm_final pmStore) 601 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [701], params := [2] } :: (segment_000000_pm_nodes.drop 4)) 601
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 602 = (segment_000000_pm_final pmStore) 602 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [701], params := [2] } :: (segment_000000_pm_nodes.drop 4)) 602
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 701 = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 1 [(segment_000000_pm_final pmStore) 600, (segment_000000_pm_final pmStore) 601, (segment_000000_pm_final pmStore) 602] := by
    calc
      _ = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 1 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 600, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 601, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 602] := hout_prefix
      _ = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 1 [(segment_000000_pm_final pmStore) 600, (segment_000000_pm_final pmStore) 601, (segment_000000_pm_final pmStore) 602] := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_scatter_writer2 (pmStore : Store) : (segment_000000_pm_final pmStore) 702 = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 2 [(segment_000000_pm_final pmStore) 600, (segment_000000_pm_final pmStore) 601, (segment_000000_pm_final pmStore) 602] := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 2, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [702], params := [2] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 702 = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 2 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 600, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 601, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 602] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 2, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [702], params := [2] } 702
      (fun t => reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 2 [t 600, t 601, t 602]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_reduceScatterPrim_out SyntheticBWSoftmaxReduceScatter.pmGraph t 2 2 [600, 601, 602] 702
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 600 = (segment_000000_pm_final pmStore) 600 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [702], params := [2] } :: (segment_000000_pm_nodes.drop 5)) 600
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 601 = (segment_000000_pm_final pmStore) 601 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [702], params := [2] } :: (segment_000000_pm_nodes.drop 5)) 601
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 602 = (segment_000000_pm_final pmStore) 602 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWSoftmaxReduceScatter.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.ReduceScatterPrim", ins := [600, 601, 602], outs := [702], params := [2] } :: (segment_000000_pm_nodes.drop 5)) 602
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 702 = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 2 [(segment_000000_pm_final pmStore) 600, (segment_000000_pm_final pmStore) 601, (segment_000000_pm_final pmStore) 602] := by
    calc
      _ = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 2 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 600, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 601, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticBWSoftmaxReduceScatter.pmGraph) pmStore 602] := hout_prefix
      _ = reduceScatterPrimDimN 2 SyntheticBWSoftmaxReduceScatter.pmGraph.numRanks 2 [(segment_000000_pm_final pmStore) 600, (segment_000000_pm_final pmStore) 601, (segment_000000_pm_final pmStore) 602] := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

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
    have hg : fg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 10) [pmFinal 100, pmFinal 101, pmFinal 102] 2 [2, 3, 15, 7] [2, 3, 5, 7] at hg
    have hx : fx.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 20) [pmFinal 200, pmFinal 201, pmFinal 202] 2 [2, 3, 15, 7] [2, 3, 5, 7] at hx
    have hgValue : smFinal 10 = allGatherPrimDimN 2 3 0 [pmFinal 100, pmFinal 101, pmFinal 102] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hxValue : smFinal 20 = allGatherPrimDimN 2 3 0 [pmFinal 200, pmFinal 201, pmFinal 202] := by
      simpa only [List.length_cons, List.length_nil] using hx.full_value
    have hSmWriter : smFinal 30 = bw_softmax (smFinal 10) (smFinal 20) :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 300 = bw_softmax (pmFinal 100) (pmFinal 200) :=
      segment_000000_hPmWriter0 pmStore
    have hOutShape0 : (pmFinal 300).shape = [2, 3, 5, 7] := by
      rw [hPmWriter0]
      exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 (hx.shard_shapes _ (by simp))
    have hPmWriter1 : pmFinal 301 = bw_softmax (pmFinal 101) (pmFinal 201) :=
      segment_000000_hPmWriter1 pmStore
    have hOutShape1 : (pmFinal 301).shape = [2, 3, 5, 7] := by
      rw [hPmWriter1]
      exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 (hx.shard_shapes _ (by simp))
    have hPmWriter2 : pmFinal 302 = bw_softmax (pmFinal 102) (pmFinal 202) :=
      segment_000000_hPmWriter2 pmStore
    have hOutShape2 : (pmFinal 302).shape = [2, 3, 5, 7] := by
      rw [hPmWriter2]
      exact bw_softmax_shape_g199 _ _ [2, 3, 5] 7 (hx.shard_shapes _ (by simp))
    have hcomm := TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim2_rank4 [pmFinal 100, pmFinal 101, pmFinal 102] [pmFinal 200, pmFinal 201, pmFinal 202] 3 2 3 5 7
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp) (by simp) hg.shard_shapes hx.shard_shapes
    have hOutValue : smFinal 30 = allGatherPrimDimN 2 3 0 [pmFinal 300, pmFinal 301, pmFinal 302] := by
      rw [hSmWriter, hgValue, hxValue, hcomm]
      simp only [List.zipWith]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
    have hOutValueList : smFinal 30 = allGatherPrimDimN 2 [pmFinal 300, pmFinal 301, pmFinal 302].length 0 [pmFinal 300, pmFinal 301, pmFinal 302] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 30).shape = [2, 3, 15, 7] := by
      rw [hSmWriter]
      exact bw_softmax_shape_g199 _ _ [2, 3, 15] 7 hx.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 30) [pmFinal 300, pmFinal 301, pmFinal 302] 2 [2, 3, 15, 7] [2, 3, 5, 7]
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
      rcases hmem with h0 | h1 | h2
      · subst piece
        exact hOutShape0
      · subst piece
        exact hOutShape1
      · subst piece
        exact hOutShape2
    have hred : fw.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ReductionRel (smFinal 50) [pmFinal 600, pmFinal 601, pmFinal 602] [2, 3, 15, 7] at hred
    have hw0 := segment_000000_scatter_writer0 pmStore
    change pmFinal 700 = reduceScatterPrimDimN 2 3 0 [pmFinal 600, pmFinal 601, pmFinal 602] at hw0
    have hr0 : smFinal 50 = allReducePrim 3 0 [pmFinal 600, pmFinal 601, pmFinal 602] := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value
    have hc0 : pmFinal 700 = chunkPrimDimN 2 3 0 (smFinal 50) := by rw [hw0]; unfold reduceScatterPrimDimN; rw [← hr0]
    have hw1 := segment_000000_scatter_writer1 pmStore
    change pmFinal 701 = reduceScatterPrimDimN 2 3 1 [pmFinal 600, pmFinal 601, pmFinal 602] at hw1
    have hr1 : smFinal 50 = allReducePrim 3 1 [pmFinal 600, pmFinal 601, pmFinal 602] := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value
    have hc1 : pmFinal 701 = chunkPrimDimN 2 3 1 (smFinal 50) := by rw [hw1]; unfold reduceScatterPrimDimN; rw [← hr1]
    have hw2 := segment_000000_scatter_writer2 pmStore
    change pmFinal 702 = reduceScatterPrimDimN 2 3 2 [pmFinal 600, pmFinal 601, pmFinal 602] at hw2
    have hr2 : smFinal 50 = allReducePrim 3 2 [pmFinal 600, pmFinal 601, pmFinal 602] := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value
    have hc2 : pmFinal 702 = chunkPrimDimN 2 3 2 (smFinal 50) := by rw [hw2]; unfold reduceScatterPrimDimN; rw [← hr2]
    have hordered : [pmFinal 700, pmFinal 701, pmFinal 702] = List.ofFn (fun r : Fin 3 => chunkPrimDimN 2 3 r.1 (smFinal 50)) := by
      change [pmFinal 700, pmFinal 701, pmFinal 702] = [chunkPrimDimN 2 3 0 (smFinal 50), chunkPrimDimN 2 3 1 (smFinal 50), chunkPrimDimN 2 3 2 (smFinal 50)]
      rw [hc0, hc1, hc2]
    have hvalue : smFinal 50 = allGatherPrimDimN 2 [pmFinal 700, pmFinal 701, pmFinal 702].length 0 [pmFinal 700, pmFinal 701, pmFinal 702] := by
      rw [hordered]
      simp only [List.length_ofFn]
      symm
      exact allGatherPrimDimN_chunks_ofFn 2 3 (smFinal 50) (by omega) (by rw [hred.full_shape]; native_decide) (by rw [hred.full_shape]; native_decide)
    have hs0 : (pmFinal 700).shape = [2, 3, 5, 7] := by
      rw [hc0, chunkPrimDimN_shape 2 3 0 (smFinal 50) [2, 3, 15, 7] hred.full_shape (by omega)]
      native_decide
    have hs1 : (pmFinal 701).shape = [2, 3, 5, 7] := by
      rw [hc1, chunkPrimDimN_shape 2 3 1 (smFinal 50) [2, 3, 15, 7] hred.full_shape (by omega)]
      native_decide
    have hs2 : (pmFinal 702).shape = [2, 3, 5, 7] := by
      rw [hc2, chunkPrimDimN_shape 2 3 2 (smFinal 50) [2, 3, 15, 7] hred.full_shape (by omega)]
      native_decide
    have houtScatter : fj.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 50) [pmFinal 700, pmFinal 701, pmFinal 702] 2 [2, 3, 15, 7] [2, 3, 5, 7]
      refine { full_value := hvalue, full_shape := hred.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp }
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hs0
      · exact hs1
      · exact hs2
    intro fact hfact
    have covered : fact ∈ [fo, fj] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fo, fj] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · exact hout
      · exact houtScatter
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticBWSoftmaxReduceScatter.smGraph SyntheticBWSoftmaxReduceScatter.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end SyntheticBWSoftmaxReduceScatter
