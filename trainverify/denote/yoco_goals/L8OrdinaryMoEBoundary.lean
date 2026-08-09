/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5430 and PM 9230/9231. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L8OrdinaryMoEDown
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

private def l8OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5413, 5426], outs := [5427] }
private def l8OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9174, 9210], outs := [9216] }
private def l8OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9175, 9211], outs := [9217] }

private def l8OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5408, 5427], outs := [5428] }
private def l8OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9164, 9216], outs := [9220] }
private def l8OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9165, 9217], outs := [9221] }

private def l8OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5428], outs := [5429] }
private def l8OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9220], outs := [9226] }
private def l8OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9221], outs := [9227] }

private def l8OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8185, 5429], outs := [5430] }
private def l8OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15714, 9226], outs := [9230] }
private def l8OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15722, 9227], outs := [9231] }

private theorem l8OMO_red_sm5427 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5427 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5413)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5426) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 349 l8OMOSmMul
    5413 5426 5427 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5413 5426 5427

private theorem l8OMO_red_pm9216 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9216 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9174)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9210) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 780 l8OMOPmMul0
    9174 9210 9216 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 9174 9210 9216

private theorem l8OMO_red_pm9217 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9217 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9175)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9211) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 781 l8OMOPmMul1
    9175 9211 9217 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 9175 9211 9217

private theorem l8OMO_red_sm5428 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5428 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5408)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5427) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 350 l8OMOSmJoin
    5408 5427 5428 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5408 5427 5428

private theorem l8OMO_red_pm9220 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9220 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9164)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9216) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 782 l8OMOPmJoin0
    9164 9216 9220 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 9164 9216 9220

private theorem l8OMO_red_pm9221 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9221 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9165)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9217) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 783 l8OMOPmJoin1
    9165 9217 9221 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 9165 9217 9221

private theorem l8OMO_red_sm5429 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5429 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5428 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 351 l8OMOSmFloat
    5428 5429 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5428 5429 []

private theorem l8OMO_red_pm9226 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9226 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9220 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 784 l8OMOPmFloat0
    9220 9226 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9220 9226 []

private theorem l8OMO_red_pm9227 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9227 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9221 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 785 l8OMOPmFloat1
    9221 9227 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9221 9227 []

private theorem l8OMO_red_sm5430 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5430 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8185)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5429) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 352 l8OMOSmOutput
    8185 5429 5430 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8185 5429 5430

private theorem l8OMO_red_pm9230 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9230 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15714)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9226) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 786 l8OMOPmOutput0
    15714 9226 9230 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15714 9226 9230

private theorem l8OMO_red_pm9231 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9231 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15722)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9227) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 787 l8OMOPmOutput1
    15722 9227 9231 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15722 9227 9231



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
theorem l8_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8185)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15714)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15722)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5408)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9164)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9165)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5413)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9174)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9175)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5426)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9211)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9230)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9231)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5427)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9217)
      [4096, 1024] [2048, 1024] := by
    rw [l8OMO_red_sm5427 initSM, l8OMO_red_pm9216 initPM, l8OMO_red_pm9217 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5428)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9220)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9221)
      [4096, 1024] [2048, 1024] := by
    rw [l8OMO_red_sm5428 initSM, l8OMO_red_pm9220 initPM, l8OMO_red_pm9221 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5429)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9226)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9227)
      [4096, 1024] [2048, 1024] := by
    rw [l8OMO_red_sm5429 initSM, l8OMO_red_pm9226 initPM, l8OMO_red_pm9227 initPM]
    exact hJoin
  rw [l8OMO_red_sm5430 initSM, l8OMO_red_pm9230 initPM, l8OMO_red_pm9231 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l8_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
