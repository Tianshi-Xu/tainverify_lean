/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5540 and PM 9558/9559. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L10OrdinaryMoEDown
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

private def l10OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5523, 5536], outs := [5537] }
private def l10OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9502, 9538], outs := [9544] }
private def l10OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9503, 9539], outs := [9545] }

private def l10OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5518, 5537], outs := [5538] }
private def l10OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9492, 9544], outs := [9548] }
private def l10OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9493, 9545], outs := [9549] }

private def l10OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5538], outs := [5539] }
private def l10OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9548], outs := [9554] }
private def l10OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9549], outs := [9555] }

private def l10OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8289, 5539], outs := [5540] }
private def l10OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15778, 9554], outs := [9558] }
private def l10OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15786, 9555], outs := [9559] }

private theorem l10OMO_red_sm5537 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5537 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5523)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5536) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 427 l10OMOSmMul
    5523 5536 5537 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5523 5536 5537

private theorem l10OMO_red_pm9544 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9544 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9502)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9538) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 948 l10OMOPmMul0
    9502 9538 9544 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 9502 9538 9544

private theorem l10OMO_red_pm9545 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9545 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9503)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9539) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 949 l10OMOPmMul1
    9503 9539 9545 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 9503 9539 9545

private theorem l10OMO_red_sm5538 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5538 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5518)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5537) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 428 l10OMOSmJoin
    5518 5537 5538 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5518 5537 5538

private theorem l10OMO_red_pm9548 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9548 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9492)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9544) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 950 l10OMOPmJoin0
    9492 9544 9548 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 9492 9544 9548

private theorem l10OMO_red_pm9549 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9549 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9493)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9545) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 951 l10OMOPmJoin1
    9493 9545 9549 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 9493 9545 9549

private theorem l10OMO_red_sm5539 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5539 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5538 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 429 l10OMOSmFloat
    5538 5539 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5538 5539 []

private theorem l10OMO_red_pm9554 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9554 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9548 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 952 l10OMOPmFloat0
    9548 9554 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9548 9554 []

private theorem l10OMO_red_pm9555 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9555 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9549 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 953 l10OMOPmFloat1
    9549 9555 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9549 9555 []

private theorem l10OMO_red_sm5540 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5540 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8289)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5539) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 430 l10OMOSmOutput
    8289 5539 5540 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8289 5539 5540

private theorem l10OMO_red_pm9558 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9558 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15778)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9554) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 954 l10OMOPmOutput0
    15778 9554 9558 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15778 9554 9558

private theorem l10OMO_red_pm9559 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9559 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15786)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9555) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 955 l10OMOPmOutput1
    15786 9555 9559 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15786 9555 9559



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
theorem l10_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8289)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15778)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15786)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5518)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9492)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9493)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5523)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9502)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9503)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5536)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9538)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9539)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5540)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9558)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9559)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5537)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9544)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9545)
      [4096, 1024] [2048, 1024] := by
    rw [l10OMO_red_sm5537 initSM, l10OMO_red_pm9544 initPM, l10OMO_red_pm9545 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5538)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9548)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9549)
      [4096, 1024] [2048, 1024] := by
    rw [l10OMO_red_sm5538 initSM, l10OMO_red_pm9548 initPM, l10OMO_red_pm9549 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5539)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9554)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9555)
      [4096, 1024] [2048, 1024] := by
    rw [l10OMO_red_sm5539 initSM, l10OMO_red_pm9554 initPM, l10OMO_red_pm9555 initPM]
    exact hJoin
  rw [l10OMO_red_sm5540 initSM, l10OMO_red_pm9558 initPM, l10OMO_red_pm9559 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l10_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
