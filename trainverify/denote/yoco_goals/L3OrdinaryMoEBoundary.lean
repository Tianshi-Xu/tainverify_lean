/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5155 and PM 8410/8411. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L3OrdinaryMoEDown
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

private def l3OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5138, 5151], outs := [5152] }
private def l3OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [8354, 8390], outs := [8396] }
private def l3OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [8355, 8391], outs := [8397] }

private def l3OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5133, 5152], outs := [5153] }
private def l3OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8344, 8396], outs := [8400] }
private def l3OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [8345, 8397], outs := [8401] }

private def l3OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5153], outs := [5154] }
private def l3OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8400], outs := [8406] }
private def l3OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [8401], outs := [8407] }

private def l3OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [7925, 5154], outs := [5155] }
private def l3OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15554, 8406], outs := [8410] }
private def l3OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15562, 8407], outs := [8411] }

private theorem l3OMO_red_sm5152 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5152 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5138)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5151) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 154 l3OMOSmMul
    5138 5151 5152 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5138 5151 5152

private theorem l3OMO_red_pm8396 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8396 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8354)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8390) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 360 l3OMOPmMul0
    8354 8390 8396 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 8354 8390 8396

private theorem l3OMO_red_pm8397 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8397 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8355)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8391) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 361 l3OMOPmMul1
    8355 8391 8397 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 8355 8391 8397

private theorem l3OMO_red_sm5153 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5153 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5133)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5152) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 155 l3OMOSmJoin
    5133 5152 5153 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5133 5152 5153

private theorem l3OMO_red_pm8400 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8400 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8344)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8396) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 362 l3OMOPmJoin0
    8344 8396 8400 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 8344 8396 8400

private theorem l3OMO_red_pm8401 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8401 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8345)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8397) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 363 l3OMOPmJoin1
    8345 8397 8401 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 8345 8397 8401

private theorem l3OMO_red_sm5154 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5154 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5153 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 156 l3OMOSmFloat
    5153 5154 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5153 5154 []

private theorem l3OMO_red_pm8406 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8406 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8400 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 364 l3OMOPmFloat0
    8400 8406 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 8400 8406 []

private theorem l3OMO_red_pm8407 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8407 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8401 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 365 l3OMOPmFloat1
    8401 8407 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 8401 8407 []

private theorem l3OMO_red_sm5155 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5155 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 7925)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5154) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 157 l3OMOSmOutput
    7925 5154 5155 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 7925 5154 5155

private theorem l3OMO_red_pm8410 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8410 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15554)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8406) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 366 l3OMOPmOutput0
    15554 8406 8410 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15554 8406 8410

private theorem l3OMO_red_pm8411 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8411 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15562)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8407) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 367 l3OMOPmOutput1
    15562 8407 8411 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15562 8407 8411



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
theorem l3_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7925)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15554)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15562)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5133)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8344)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8345)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5138)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8355)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5151)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8390)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8391)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5155)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8410)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8411)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5152)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8396)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8397)
      [4096, 1024] [2048, 1024] := by
    rw [l3OMO_red_sm5152 initSM, l3OMO_red_pm8396 initPM, l3OMO_red_pm8397 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5153)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8400)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8401)
      [4096, 1024] [2048, 1024] := by
    rw [l3OMO_red_sm5153 initSM, l3OMO_red_pm8400 initPM, l3OMO_red_pm8401 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5154)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8406)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8407)
      [4096, 1024] [2048, 1024] := by
    rw [l3OMO_red_sm5154 initSM, l3OMO_red_pm8406 initPM, l3OMO_red_pm8407 initPM]
    exact hJoin
  rw [l3OMO_red_sm5155 initSM, l3OMO_red_pm8410 initPM, l3OMO_red_pm8411 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l3_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
