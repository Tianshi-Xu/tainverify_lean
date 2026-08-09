/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5265 and PM 8738/8739. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L5OrdinaryMoEDown
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

private def l5OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5248, 5261], outs := [5262] }
private def l5OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [8682, 8718], outs := [8724] }
private def l5OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [8683, 8719], outs := [8725] }

private def l5OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5243, 5262], outs := [5263] }
private def l5OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8672, 8724], outs := [8728] }
private def l5OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [8673, 8725], outs := [8729] }

private def l5OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5263], outs := [5264] }
private def l5OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8728], outs := [8734] }
private def l5OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [8729], outs := [8735] }

private def l5OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8029, 5264], outs := [5265] }
private def l5OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15618, 8734], outs := [8738] }
private def l5OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15626, 8735], outs := [8739] }

private theorem l5OMO_red_sm5262 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5262 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5248)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5261) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 232 l5OMOSmMul
    5248 5261 5262 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5248 5261 5262

private theorem l5OMO_red_pm8724 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8724 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8682)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8718) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 528 l5OMOPmMul0
    8682 8718 8724 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 8682 8718 8724

private theorem l5OMO_red_pm8725 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8725 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8683)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8719) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 529 l5OMOPmMul1
    8683 8719 8725 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 8683 8719 8725

private theorem l5OMO_red_sm5263 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5263 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5243)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5262) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 233 l5OMOSmJoin
    5243 5262 5263 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5243 5262 5263

private theorem l5OMO_red_pm8728 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8728 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8672)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8724) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 530 l5OMOPmJoin0
    8672 8724 8728 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 8672 8724 8728

private theorem l5OMO_red_pm8729 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8729 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8673)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8725) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 531 l5OMOPmJoin1
    8673 8725 8729 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 8673 8725 8729

private theorem l5OMO_red_sm5264 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5264 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5263 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 234 l5OMOSmFloat
    5263 5264 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5263 5264 []

private theorem l5OMO_red_pm8734 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8734 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8728 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 532 l5OMOPmFloat0
    8728 8734 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 8728 8734 []

private theorem l5OMO_red_pm8735 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8735 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8729 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 533 l5OMOPmFloat1
    8729 8735 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 8729 8735 []

private theorem l5OMO_red_sm5265 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5265 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8029)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5264) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 235 l5OMOSmOutput
    8029 5264 5265 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8029 5264 5265

private theorem l5OMO_red_pm8738 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8738 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15618)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8734) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 534 l5OMOPmOutput0
    15618 8734 8738 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15618 8734 8738

private theorem l5OMO_red_pm8739 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8739 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15626)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8735) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 535 l5OMOPmOutput1
    15626 8735 8739 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15626 8735 8739



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
theorem l5_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8029)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15618)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15626)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5243)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8672)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8673)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5248)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8682)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8683)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5261)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8718)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8719)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5265)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8739)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5262)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8724)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8725)
      [4096, 1024] [2048, 1024] := by
    rw [l5OMO_red_sm5262 initSM, l5OMO_red_pm8724 initPM, l5OMO_red_pm8725 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5263)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8728)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8729)
      [4096, 1024] [2048, 1024] := by
    rw [l5OMO_red_sm5263 initSM, l5OMO_red_pm8728 initPM, l5OMO_red_pm8729 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5264)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8734)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8735)
      [4096, 1024] [2048, 1024] := by
    rw [l5OMO_red_sm5264 initSM, l5OMO_red_pm8734 initPM, l5OMO_red_pm8735 initPM]
    exact hJoin
  rw [l5OMO_red_sm5265 initSM, l5OMO_red_pm8738 initPM, l5OMO_red_pm8739 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l5_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
