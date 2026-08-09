/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5100 and PM 8246/8247. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L2OrdinaryMoEDown
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

private def l2OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5083, 5096], outs := [5097] }
private def l2OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [8190, 8226], outs := [8232] }
private def l2OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [8191, 8227], outs := [8233] }

private def l2OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5078, 5097], outs := [5098] }
private def l2OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8180, 8232], outs := [8236] }
private def l2OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [8181, 8233], outs := [8237] }

private def l2OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5098], outs := [5099] }
private def l2OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8236], outs := [8242] }
private def l2OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [8237], outs := [8243] }

private def l2OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [7873, 5099], outs := [5100] }
private def l2OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15522, 8242], outs := [8246] }
private def l2OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15530, 8243], outs := [8247] }

private theorem l2OMO_red_sm5097 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5097 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5083)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5096) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 115 l2OMOSmMul
    5083 5096 5097 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5083 5096 5097

private theorem l2OMO_red_pm8232 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8232 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8190)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8226) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 276 l2OMOPmMul0
    8190 8226 8232 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 8190 8226 8232

private theorem l2OMO_red_pm8233 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8233 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8191)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8227) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 277 l2OMOPmMul1
    8191 8227 8233 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 8191 8227 8233

private theorem l2OMO_red_sm5098 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5098 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5078)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5097) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 116 l2OMOSmJoin
    5078 5097 5098 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5078 5097 5098

private theorem l2OMO_red_pm8236 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8236 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8180)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8232) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 278 l2OMOPmJoin0
    8180 8232 8236 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 8180 8232 8236

private theorem l2OMO_red_pm8237 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8237 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8181)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8233) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 279 l2OMOPmJoin1
    8181 8233 8237 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 8181 8233 8237

private theorem l2OMO_red_sm5099 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5099 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5098 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 117 l2OMOSmFloat
    5098 5099 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5098 5099 []

private theorem l2OMO_red_pm8242 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8242 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8236 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 280 l2OMOPmFloat0
    8236 8242 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 8236 8242 []

private theorem l2OMO_red_pm8243 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8243 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8237 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 281 l2OMOPmFloat1
    8237 8243 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 8237 8243 []

private theorem l2OMO_red_sm5100 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5100 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 7873)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5099) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 118 l2OMOSmOutput
    7873 5099 5100 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 7873 5099 5100

private theorem l2OMO_red_pm8246 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8246 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15522)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8242) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 282 l2OMOPmOutput0
    15522 8242 8246 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15522 8242 8246

private theorem l2OMO_red_pm8247 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8247 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15530)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8243) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 283 l2OMOPmOutput1
    15530 8243 8247 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15530 8243 8247



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
theorem l2_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7873)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15522)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15530)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5078)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8180)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8181)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5083)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8190)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8191)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5096)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8226)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8227)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8246)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8247)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5097)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8233)
      [4096, 1024] [2048, 1024] := by
    rw [l2OMO_red_sm5097 initSM, l2OMO_red_pm8232 initPM, l2OMO_red_pm8233 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5098)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8236)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8237)
      [4096, 1024] [2048, 1024] := by
    rw [l2OMO_red_sm5098 initSM, l2OMO_red_pm8236 initPM, l2OMO_red_pm8237 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5099)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8242)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8243)
      [4096, 1024] [2048, 1024] := by
    rw [l2OMO_red_sm5099 initSM, l2OMO_red_pm8242 initPM, l2OMO_red_pm8243 initPM]
    exact hJoin
  rw [l2OMO_red_sm5100 initSM, l2OMO_red_pm8246 initPM, l2OMO_red_pm8247 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l2_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
