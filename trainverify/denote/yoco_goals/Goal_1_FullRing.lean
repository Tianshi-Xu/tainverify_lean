import denote.yoco_goals.Pattern_1
import denote.yoco_goals.ZigzagL11Body
import denote.yoco_goals.YOCOStructuralFacts
import denote.yoco_goals.BridgeKit
import denote.yoco_goals.RingFixedPointBridge
import denote.yoco_goals.RingTailBridge

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedGoals

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote.GeneratedStructuralFacts

private theorem sm_nodes_nonempty : ∀ n ∈ sm.nodes, n.outs ≠ [] := by native_decide
private theorem pm_nodes_nonempty : ∀ n ∈ pm.nodes, n.outs ≠ [] := by native_decide

/-- Full ring-aware Goal 1 statement under the labels-in-vocabulary and YOCO
input contracts. -/
def goal_1_stmt_ringAttn_full_with_labels : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM smInitEnv →
    StoreShapesHold initPM pmInitEnv →
    InitGoalsHold pm.numRanks initGoals initSM initPM →
    WellFormed_YOCOMoE_A04B initSM initPM →
    (∀ l : Nat, l < 4096 →
      scalarToNat (valAt (denoteGraph_ringAttn pm initPM 4678) l) < 154880) →
    InitGoalHolds pm.numRanks goal_1
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)

private theorem red_sm4673 (initSM : Store) :
    denoteGraph_ringAttn sm initSM 4673 =
      (fw_inner_chunk_ce (denoteGraph_ringAttn sm initSM 5930)
        (denoteGraph_ringAttn sm initSM 5931)
        (denoteGraph_ringAttn sm initSM 4678)
        (((denoteGraph_ringAttn sm initSM 5931).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst := by
  have hf := node_fixed_on_ring_final sm initSM 926
    { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [5930, 5931, 4678],
      outs := [4673, 4674], params := [1024] }
    (by native_decide) (by native_decide) (sm_wellFormed _ (by native_decide))
    (by decide) (by decide) sm_nodes_nonempty (by native_decide) (by native_decide)
  have hv := congrFun hf 4673
  rw [applyNode_fw_inner_chunk_ce_fst_out_1p sm _ 0 5930 5931 4678 4673 4674 [1024]] at hv
  exact hv.symm

private theorem red_pm11835 (initPM : Store) :
    denoteGraph_ringAttn pm initPM 11835 =
      chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 4678) := by
  have hf := node_fixed_on_ring_final pm initPM 12
    { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] }
    (by native_decide) (by native_decide) (pm_wellFormed _ (by native_decide))
    (by decide) (by decide) pm_nodes_nonempty (by native_decide) (by native_decide)
  have hv := congrFun hf 11835
  rw [applyNode_chunkPrimDimN_out pm _ 0 4678 11835 0] at hv
  exact hv.symm

private theorem red_pm11836 (initPM : Store) :
    denoteGraph_ringAttn pm initPM 11836 =
      chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 4678) := by
  have hf := node_fixed_on_ring_final pm initPM 25
    { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] }
    (by native_decide) (by native_decide) (pm_wellFormed _ (by native_decide))
    (by decide) (by decide) pm_nodes_nonempty (by native_decide) (by native_decide)
  have hv := congrFun hf 11836
  rw [applyNode_chunkPrimDimN_out pm _ 1 4678 11836 0] at hv
  exact hv.symm

private theorem red_pm11837 (initPM : Store) :
    denoteGraph_ringAttn pm initPM 11837 =
      (fw_inner_chunk_ce (denoteGraph_ringAttn pm initPM 11833)
        (denoteGraph_ringAttn pm initPM 5931)
        (denoteGraph_ringAttn pm initPM 11835)
        (((denoteGraph_ringAttn pm initPM 5931).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst := by
  have hf := node_fixed_on_ring_final pm initPM 1916
    { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835],
      outs := [11837, 11839], params := [1024] }
    (by native_decide) (by native_decide) (pm_wellFormed _ (by native_decide))
    (by decide) (by decide) pm_nodes_nonempty (by native_decide) (by native_decide)
  have hv := congrFun hf 11837
  rw [applyNode_fw_inner_chunk_ce_fst_out_1p pm _ 0 11833 5931 11835 11837 11839 [1024]] at hv
  exact hv.symm

private theorem red_pm11838 (initPM : Store) :
    denoteGraph_ringAttn pm initPM 11838 =
      (fw_inner_chunk_ce (denoteGraph_ringAttn pm initPM 11834)
        (denoteGraph_ringAttn pm initPM 5931)
        (denoteGraph_ringAttn pm initPM 11836)
        (((denoteGraph_ringAttn pm initPM 5931).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst := by
  have hf := node_fixed_on_ring_final pm initPM 1917
    { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836],
      outs := [11838, 11840], params := [1024] }
    (by native_decide) (by native_decide) (pm_wellFormed _ (by native_decide))
    (by decide) (by decide) pm_nodes_nonempty (by native_decide) (by native_decide)
  have hv := congrFun hf 11838
  rw [applyNode_fw_inner_chunk_ce_fst_out_1p pm _ 1 11834 5931 11836 11838 11840 [1024]] at hv
  exact hv.symm

private theorem red_pm4673 (initPM : Store) :
    denoteGraph_ringAttn pm initPM 4673 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm initPM 11837,
         denoteGraph_ringAttn pm initPM 11838] := by
  have hf := node_fixed_on_ring_final pm initPM 1918
    { rank := 0, op := "OpName.AllGatherPrim", ins := [11837, 11838],
      outs := [4673], params := [0] }
    (by native_decide) (by native_decide) (pm_wellFormed _ (by native_decide))
    (by decide) (by decide) pm_nodes_nonempty (by native_decide) (by native_decide)
  have hv := congrFun hf 4673
  rw [applyNode_allGatherPrimDimN_out pm _ 0 [11837, 11838] 4673 0] at hv
  exact hv.symm

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem prove_goal_1_ringAttn_full : goal_1_stmt_ringAttn_full_with_labels := by
  intro initSM initPM hSM hPM hInit hWF hlabels
  have hnorm := recon_intermediateGoal_5930_ringAttn initSM initPM hSM hPM hInit hWF
  obtain ⟨hnormVal, hxa, hxb⟩ := twoTp_gather _ _ intermediateGoal_5930
    5930 11833 11834 [2048, 1024] rfl rfl rfl rfl rfl (by decide) hnorm
  have hwEq : denoteGraph_ringAttn sm initSM 5931 =
      denoteGraph_ringAttn pm initPM 5931 :=
    veq_weight_ring initSM initPM hInit initGoal_5931 (by native_decide) 5931
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hyEq : denoteGraph_ringAttn sm initSM 4678 =
      denoteGraph_ringAttn pm initPM 4678 :=
    veq_weight_ring initSM initPM hInit initGoal_4678 (by native_decide) 4678
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hbase := initGoals_preserved_ringAttn initSM initPM hInit
  have hwGoal := hbase initGoal_5931 (by native_decide)
  have hyGoal := hbase initGoal_4678 (by native_decide)
  have hw : (denoteGraph_ringAttn pm initPM 5931).shape = [154880, 1024] := by
    have hp := congrArg (fun xs => xs.getD 0 []) hwGoal.2.1
    simpa [initGoal_5931] using hp
  have hy : (denoteGraph_ringAttn pm initPM 4678).shape = [4096] := by
    have hp := congrArg (fun xs => xs.getD 0 []) hyGoal.2.1
    simpa [initGoal_4678] using hp
  have hvocab : ((denoteGraph_ringAttn pm initPM 5931).shape.head?).getD 0 = 154880 := by
    rw [hw]
    rfl
  have hnr : pm.numRanks = 2 := rfl
  have hval : denoteGraph_ringAttn sm initSM 4673 =
      denoteGraph_ringAttn pm initPM 4673 := by
    rw [red_sm4673, red_pm4673, red_pm11837, red_pm11838,
      red_pm11835, red_pm11836, hwEq, hyEq, hnormVal, hvocab, hnr]
    exact fw_inner_chunk_ce_fst_allGather0_commute_2_of
      (denoteGraph_ringAttn pm initPM 11833)
      (denoteGraph_ringAttn pm initPM 11834)
      (denoteGraph_ringAttn pm initPM 5931)
      (denoteGraph_ringAttn pm initPM 4678)
      2048 1024 154880 (by decide) (by decide) (by decide)
      hxa hxb hw hy hlabels ((0 : Nat) : Scalar)
  have hxShape : (denoteGraph_ringAttn sm initSM 5930).shape = [4096, 1024] := by
    simpa [intermediateGoal_5930] using hnorm.1
  have hsmShape : (denoteGraph_ringAttn sm initSM 4673).shape = [4096] := by
    rw [red_sm4673]
    apply fw_inner_chunk_ce_fst_shape
    rw [hxShape]
    rfl
  have hpmShape : (denoteGraph_ringAttn pm initPM 4673).shape = [4096] := by
    rw [← hval]
    exact hsmShape
  refine ⟨hsmShape, ?_, ?_⟩
  · simp [goal_1, hpmShape]
  · simpa [goal_1, reconstructForGoal, reconstructWithDim] using hval

end TrainVerify.Denote.GeneratedGoals
