/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5595 and PM 9722/9723. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.CanonicalKVCacheOrdinaryDown
import denote.yoco_goals.FaithfulStackGather
import denote.yoco_goals.ZigzagBroadcastMul
import denote.yoco_goals.ZigzagPointwiseRel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def cKVCOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5578, 5591], outs := [5592] }
private def cKVCOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9666, 9702], outs := [9708] }
private def cKVCOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9667, 9703], outs := [9709] }

private def cKVCOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5573, 5592], outs := [5593] }
private def cKVCOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9656, 9708], outs := [9712] }
private def cKVCOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9657, 9709], outs := [9713] }

private def cKVCOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5593], outs := [5594] }
private def cKVCOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9712], outs := [9718] }
private def cKVCOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9713], outs := [9719] }

private def cKVCOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8341, 5594], outs := [5595] }
private def cKVCOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15810, 9718], outs := [9722] }
private def cKVCOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15818, 9719], outs := [9723] }

private theorem cKVCO_red_sm5592 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5592 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5578)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5591) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 466 cKVCOSmMul
    5578 5591 5592 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5578 5591 5592

private theorem cKVCO_red_pm9708 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9708 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9666)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9702) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1032 cKVCOPmMul0
    9666 9702 9708 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 9666 9702 9708

private theorem cKVCO_red_pm9709 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9709 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9667)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9703) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1033 cKVCOPmMul1
    9667 9703 9709 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 9667 9703 9709

private theorem cKVCO_red_sm5593 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5593 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5573)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5592) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 467 cKVCOSmJoin
    5573 5592 5593 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5573 5592 5593

private theorem cKVCO_red_pm9712 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9712 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9656)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9708) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1034 cKVCOPmJoin0
    9656 9708 9712 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 9656 9708 9712

private theorem cKVCO_red_pm9713 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9713 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9657)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9709) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1035 cKVCOPmJoin1
    9657 9709 9713 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 9657 9709 9713

private theorem cKVCO_red_sm5594 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5594 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5593 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 468 cKVCOSmFloat
    5593 5594 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5593 5594 []

private theorem cKVCO_red_pm9718 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9718 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9712 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1036 cKVCOPmFloat0
    9712 9718 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9712 9718 []

private theorem cKVCO_red_pm9719 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9719 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9713 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1037 cKVCOPmFloat1
    9713 9719 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9713 9719 []

private theorem cKVCO_red_sm5595 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5595 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8341)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5594) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 469 cKVCOSmOutput
    8341 5594 5595 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8341 5594 5595

private theorem cKVCO_red_pm9722 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9722 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15810)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9718) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1038 cKVCOPmOutput0
    15810 9718 9722 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15810 9718 9722

private theorem cKVCO_red_pm9723 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9723 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15818)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9719) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1039 cKVCOPmOutput1
    15818 9719 9723 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15818 9719 9723



private theorem ordinary_mul_broadcast
    {fullA rankA0 rankA1 fullB rankB0 rankB1 : Tensor} (lDim d : Nat)
    (hA : Ordinary2Rel fullA rankA0 rankA1 [lDim * 2, 1] [lDim, 1])
    (hB : Ordinary2Rel fullB rankB0 rankB1 [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    Ordinary2Rel (elemwiseMul fullA fullB) (elemwiseMul rankA0 rankB0)
      (elemwiseMul rankA1 rankB1) [lDim * 2, d] [lDim, d] := by
  refine {
    full_value := ?_
    full_shape := ZigzagBroadcastMul.elemwiseMul_shape_col1 fullA fullB
      (lDim * 2) d hA.full_shape hB.full_shape hd
    rank0_shape := ZigzagBroadcastMul.elemwiseMul_shape_col1 rankA0 rankB0
      lDim d hA.rank0_shape hB.rank0_shape hd
    rank1_shape := ZigzagBroadcastMul.elemwiseMul_shape_col1 rankA1 rankB1
      lDim d hA.rank1_shape hB.rank1_shape hd
  }
  rw [hA.full_value, hB.full_value]
  exact ZigzagBroadcastMul.mulBC_allGather0_commute_cp2
    rankA0 rankA1 rankB0 rankB1 lDim d hl hd
    hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

private theorem ordinary_add
    {fullA rankA0 rankA1 fullB rankB0 rankB1 : Tensor} (lDim d : Nat)
    (hA : Ordinary2Rel fullA rankA0 rankA1 [lDim * 2, d] [lDim, d])
    (hB : Ordinary2Rel fullB rankB0 rankB1 [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    Ordinary2Rel (elemwiseAdd fullA fullB) (elemwiseAdd rankA0 rankB0)
      (elemwiseAdd rankA1 rankB1) [lDim * 2, d] [lDim, d] := by
  refine {
    full_value := ?_
    full_shape := elemwiseAdd_shape_of_shapes fullA fullB [lDim * 2, d]
      hA.full_shape hB.full_shape
    rank0_shape := elemwiseAdd_shape_of_shapes rankA0 rankB0 [lDim, d]
      hA.rank0_shape hB.rank0_shape
    rank1_shape := elemwiseAdd_shape_of_shapes rankA1 rankB1 [lDim, d]
      hA.rank1_shape hB.rank1_shape
  }
  rw [hA.full_value, hB.full_value]
  exact elemwiseAdd_allGather0_commute_cp2 rankA0 rankA1 rankB0 rankB1
    lDim d hl hd hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary cache boundary tail through gate multiplication, expert
join, float, and residual add.  Every node in the tail is faithfully reduced. -/
theorem canonical_kv_cache_ordinary_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8341)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15810)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15818)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5573)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9656)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9657)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9667)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5591)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9702)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9703)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5592)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9708)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9709)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCO_red_sm5592 initSM, cKVCO_red_pm9708 initPM, cKVCO_red_pm9709 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5593)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9712)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9713)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCO_red_sm5593 initSM, cKVCO_red_pm9712 initPM, cKVCO_red_pm9713 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5594)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9718)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9719)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCO_red_sm5594 initSM, cKVCO_red_pm9718 initPM, cKVCO_red_pm9719 initPM]
    exact hJoin
  rw [cKVCO_red_sm5595 initSM, cKVCO_red_pm9722 initPM, cKVCO_red_pm9723 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms canonical_kv_cache_ordinary_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
