/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5320 and PM 8902/8903. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L6OrdinaryMoEDown
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

private def l6OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5303, 5316], outs := [5317] }
private def l6OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [8846, 8882], outs := [8888] }
private def l6OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [8847, 8883], outs := [8889] }

private def l6OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5298, 5317], outs := [5318] }
private def l6OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8836, 8888], outs := [8892] }
private def l6OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [8837, 8889], outs := [8893] }

private def l6OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5318], outs := [5319] }
private def l6OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8892], outs := [8898] }
private def l6OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [8893], outs := [8899] }

private def l6OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8081, 5319], outs := [5320] }
private def l6OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15650, 8898], outs := [8902] }
private def l6OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15658, 8899], outs := [8903] }

private theorem l6OMO_red_sm5317 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5317 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5303)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5316) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 271 l6OMOSmMul
    5303 5316 5317 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5303 5316 5317

private theorem l6OMO_red_pm8888 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8888 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8846)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8882) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 612 l6OMOPmMul0
    8846 8882 8888 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 8846 8882 8888

private theorem l6OMO_red_pm8889 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8889 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8847)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8883) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 613 l6OMOPmMul1
    8847 8883 8889 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 8847 8883 8889

private theorem l6OMO_red_sm5318 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5318 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5298)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5317) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 272 l6OMOSmJoin
    5298 5317 5318 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5298 5317 5318

private theorem l6OMO_red_pm8892 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8892 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8836)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8888) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 614 l6OMOPmJoin0
    8836 8888 8892 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 8836 8888 8892

private theorem l6OMO_red_pm8893 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8893 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8837)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8889) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 615 l6OMOPmJoin1
    8837 8889 8893 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 8837 8889 8893

private theorem l6OMO_red_sm5319 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5319 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5318 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 273 l6OMOSmFloat
    5318 5319 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5318 5319 []

private theorem l6OMO_red_pm8898 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8898 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8892 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 616 l6OMOPmFloat0
    8892 8898 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 8892 8898 []

private theorem l6OMO_red_pm8899 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8899 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8893 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 617 l6OMOPmFloat1
    8893 8899 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 8893 8899 []

private theorem l6OMO_red_sm5320 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5320 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8081)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5319) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 274 l6OMOSmOutput
    8081 5319 5320 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8081 5319 5320

private theorem l6OMO_red_pm8902 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8902 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15650)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8898) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 618 l6OMOPmOutput0
    15650 8898 8902 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15650 8898 8902

private theorem l6OMO_red_pm8903 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8903 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15658)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8899) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 619 l6OMOPmOutput1
    15658 8899 8903 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15658 8899 8903



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
theorem l6_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8081)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15650)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15658)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5298)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8837)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5303)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8846)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8847)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5316)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8882)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8883)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5320)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8902)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8903)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5317)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8888)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8889)
      [4096, 1024] [2048, 1024] := by
    rw [l6OMO_red_sm5317 initSM, l6OMO_red_pm8888 initPM, l6OMO_red_pm8889 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5318)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8893)
      [4096, 1024] [2048, 1024] := by
    rw [l6OMO_red_sm5318 initSM, l6OMO_red_pm8892 initPM, l6OMO_red_pm8893 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5319)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8898)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8899)
      [4096, 1024] [2048, 1024] := by
    rw [l6OMO_red_sm5319 initSM, l6OMO_red_pm8898 initPM, l6OMO_red_pm8899 initPM]
    exact hJoin
  rw [l6OMO_red_sm5320 initSM, l6OMO_red_pm8902 initPM, l6OMO_red_pm8903 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l6_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
