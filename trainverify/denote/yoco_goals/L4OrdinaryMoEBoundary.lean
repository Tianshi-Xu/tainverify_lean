/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5210 and PM 8574/8575. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L4OrdinaryMoEDown
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

private def l4OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5193, 5206], outs := [5207] }
private def l4OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [8518, 8554], outs := [8560] }
private def l4OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [8519, 8555], outs := [8561] }

private def l4OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5188, 5207], outs := [5208] }
private def l4OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8508, 8560], outs := [8564] }
private def l4OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [8509, 8561], outs := [8565] }

private def l4OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5208], outs := [5209] }
private def l4OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8564], outs := [8570] }
private def l4OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [8565], outs := [8571] }

private def l4OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [7977, 5209], outs := [5210] }
private def l4OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15586, 8570], outs := [8574] }
private def l4OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15594, 8571], outs := [8575] }

private theorem l4OMO_red_sm5207 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5207 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5193)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5206) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 193 l4OMOSmMul
    5193 5206 5207 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5193 5206 5207

private theorem l4OMO_red_pm8560 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8560 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8518)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8554) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 444 l4OMOPmMul0
    8518 8554 8560 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 8518 8554 8560

private theorem l4OMO_red_pm8561 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8561 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8519)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8555) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 445 l4OMOPmMul1
    8519 8555 8561 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 8519 8555 8561

private theorem l4OMO_red_sm5208 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5208 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5188)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5207) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 194 l4OMOSmJoin
    5188 5207 5208 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5188 5207 5208

private theorem l4OMO_red_pm8564 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8564 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8508)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8560) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 446 l4OMOPmJoin0
    8508 8560 8564 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 8508 8560 8564

private theorem l4OMO_red_pm8565 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8565 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8509)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8561) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 447 l4OMOPmJoin1
    8509 8561 8565 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 8509 8561 8565

private theorem l4OMO_red_sm5209 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5209 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5208 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 195 l4OMOSmFloat
    5208 5209 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5208 5209 []

private theorem l4OMO_red_pm8570 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8570 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8564 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 448 l4OMOPmFloat0
    8564 8570 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 8564 8570 []

private theorem l4OMO_red_pm8571 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8571 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8565 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 449 l4OMOPmFloat1
    8565 8571 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 8565 8571 []

private theorem l4OMO_red_sm5210 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5210 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 7977)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5209) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 196 l4OMOSmOutput
    7977 5209 5210 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 7977 5209 5210

private theorem l4OMO_red_pm8574 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8574 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15586)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8570) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 450 l4OMOPmOutput0
    15586 8570 8574 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15586 8570 8574

private theorem l4OMO_red_pm8575 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8575 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15594)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8571) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 451 l4OMOPmOutput1
    15594 8571 8575 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15594 8571 8575



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
theorem l4_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15586)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15594)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5188)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8508)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8509)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8518)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8519)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8554)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8555)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8574)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8575)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5207)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8560)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8561)
      [4096, 1024] [2048, 1024] := by
    rw [l4OMO_red_sm5207 initSM, l4OMO_red_pm8560 initPM, l4OMO_red_pm8561 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5208)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8564)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8565)
      [4096, 1024] [2048, 1024] := by
    rw [l4OMO_red_sm5208 initSM, l4OMO_red_pm8564 initPM, l4OMO_red_pm8565 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5209)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8570)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8571)
      [4096, 1024] [2048, 1024] := by
    rw [l4OMO_red_sm5209 initSM, l4OMO_red_pm8570 initPM, l4OMO_red_pm8571 initPM]
    exact hJoin
  rw [l4OMO_red_sm5210 initSM, l4OMO_red_pm8574 initPM, l4OMO_red_pm8575 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l4_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
