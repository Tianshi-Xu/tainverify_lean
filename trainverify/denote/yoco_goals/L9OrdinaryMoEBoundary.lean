/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5485 and PM 9394/9395. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L9OrdinaryMoEDown
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

private def l9OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5468, 5481], outs := [5482] }
private def l9OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9338, 9374], outs := [9380] }
private def l9OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9339, 9375], outs := [9381] }

private def l9OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5463, 5482], outs := [5483] }
private def l9OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9328, 9380], outs := [9384] }
private def l9OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9329, 9381], outs := [9385] }

private def l9OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5483], outs := [5484] }
private def l9OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9384], outs := [9390] }
private def l9OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9385], outs := [9391] }

private def l9OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8237, 5484], outs := [5485] }
private def l9OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15746, 9390], outs := [9394] }
private def l9OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15754, 9391], outs := [9395] }

private theorem l9OMO_red_sm5482 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5482 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5468)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5481) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 388 l9OMOSmMul
    5468 5481 5482 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5468 5481 5482

private theorem l9OMO_red_pm9380 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9380 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9338)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9374) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 864 l9OMOPmMul0
    9338 9374 9380 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 9338 9374 9380

private theorem l9OMO_red_pm9381 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9381 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9339)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9375) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 865 l9OMOPmMul1
    9339 9375 9381 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 9339 9375 9381

private theorem l9OMO_red_sm5483 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5483 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5463)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5482) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 389 l9OMOSmJoin
    5463 5482 5483 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5463 5482 5483

private theorem l9OMO_red_pm9384 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9384 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9328)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9380) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 866 l9OMOPmJoin0
    9328 9380 9384 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 9328 9380 9384

private theorem l9OMO_red_pm9385 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9385 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9329)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9381) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 867 l9OMOPmJoin1
    9329 9381 9385 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 9329 9381 9385

private theorem l9OMO_red_sm5484 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5484 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5483 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 390 l9OMOSmFloat
    5483 5484 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5483 5484 []

private theorem l9OMO_red_pm9390 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9390 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9384 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 868 l9OMOPmFloat0
    9384 9390 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9384 9390 []

private theorem l9OMO_red_pm9391 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9391 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9385 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 869 l9OMOPmFloat1
    9385 9391 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9385 9391 []

private theorem l9OMO_red_sm5485 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5485 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8237)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5484) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 391 l9OMOSmOutput
    8237 5484 5485 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8237 5484 5485

private theorem l9OMO_red_pm9394 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9394 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15746)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9390) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 870 l9OMOPmOutput0
    15746 9390 9394 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15746 9390 9394

private theorem l9OMO_red_pm9395 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9395 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15754)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9391) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 871 l9OMOPmOutput1
    15754 9391 9395 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15754 9391 9395



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
theorem l9_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8237)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15746)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15754)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5463)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9328)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9329)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5468)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9338)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9339)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5481)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9374)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9375)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5485)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9394)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9395)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5482)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9380)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9381)
      [4096, 1024] [2048, 1024] := by
    rw [l9OMO_red_sm5482 initSM, l9OMO_red_pm9380 initPM, l9OMO_red_pm9381 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5483)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9384)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9385)
      [4096, 1024] [2048, 1024] := by
    rw [l9OMO_red_sm5483 initSM, l9OMO_red_pm9384 initPM, l9OMO_red_pm9385 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5484)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9390)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9391)
      [4096, 1024] [2048, 1024] := by
    rw [l9OMO_red_sm5484 initSM, l9OMO_red_pm9390 initPM, l9OMO_red_pm9391 initPM]
    exact hJoin
  rw [l9OMO_red_sm5485 initSM, l9OMO_red_pm9394 initPM, l9OMO_red_pm9395 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l9_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
