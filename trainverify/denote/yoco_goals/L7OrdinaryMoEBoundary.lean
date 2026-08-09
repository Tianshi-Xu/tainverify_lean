/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5375 and PM 9066/9067. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L7OrdinaryMoEDown
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

private def l7OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5358, 5371], outs := [5372] }
private def l7OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9010, 9046], outs := [9052] }
private def l7OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9011, 9047], outs := [9053] }

private def l7OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5353, 5372], outs := [5373] }
private def l7OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9000, 9052], outs := [9056] }
private def l7OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9001, 9053], outs := [9057] }

private def l7OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5373], outs := [5374] }
private def l7OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9056], outs := [9062] }
private def l7OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9057], outs := [9063] }

private def l7OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8133, 5374], outs := [5375] }
private def l7OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15682, 9062], outs := [9066] }
private def l7OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15690, 9063], outs := [9067] }

private theorem l7OMO_red_sm5372 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5372 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5358)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5371) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 310 l7OMOSmMul
    5358 5371 5372 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5358 5371 5372

private theorem l7OMO_red_pm9052 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9052 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9010)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9046) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 696 l7OMOPmMul0
    9010 9046 9052 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 9010 9046 9052

private theorem l7OMO_red_pm9053 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9053 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9011)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9047) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 697 l7OMOPmMul1
    9011 9047 9053 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 9011 9047 9053

private theorem l7OMO_red_sm5373 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5373 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5353)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5372) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 311 l7OMOSmJoin
    5353 5372 5373 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5353 5372 5373

private theorem l7OMO_red_pm9056 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9056 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9000)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9052) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 698 l7OMOPmJoin0
    9000 9052 9056 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 9000 9052 9056

private theorem l7OMO_red_pm9057 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9057 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9001)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9053) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 699 l7OMOPmJoin1
    9001 9053 9057 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 9001 9053 9057

private theorem l7OMO_red_sm5374 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5374 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5373 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 312 l7OMOSmFloat
    5373 5374 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5373 5374 []

private theorem l7OMO_red_pm9062 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9062 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9056 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 700 l7OMOPmFloat0
    9056 9062 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9056 9062 []

private theorem l7OMO_red_pm9063 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9063 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9057 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 701 l7OMOPmFloat1
    9057 9063 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9057 9063 []

private theorem l7OMO_red_sm5375 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5375 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8133)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5374) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 313 l7OMOSmOutput
    8133 5374 5375 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8133 5374 5375

private theorem l7OMO_red_pm9066 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9066 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15682)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9062) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 702 l7OMOPmOutput0
    15682 9062 9066 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15682 9062 9066

private theorem l7OMO_red_pm9067 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9067 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15690)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9063) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 703 l7OMOPmOutput1
    15690 9063 9067 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15690 9063 9067



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
theorem l7_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8133)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15682)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15690)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5353)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9001)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5358)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9010)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9011)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5371)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9047)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5375)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9066)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9067)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5372)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9053)
      [4096, 1024] [2048, 1024] := by
    rw [l7OMO_red_sm5372 initSM, l7OMO_red_pm9052 initPM, l7OMO_red_pm9053 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5373)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9056)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9057)
      [4096, 1024] [2048, 1024] := by
    rw [l7OMO_red_sm5373 initSM, l7OMO_red_pm9056 initPM, l7OMO_red_pm9057 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5374)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9062)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9063)
      [4096, 1024] [2048, 1024] := by
    rw [l7OMO_red_sm5374 initSM, l7OMO_red_pm9062 initPM, l7OMO_red_pm9063 initPM]
    exact hJoin
  rw [l7OMO_red_sm5375 initSM, l7OMO_red_pm9066 initPM, l7OMO_red_pm9067 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l7_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
