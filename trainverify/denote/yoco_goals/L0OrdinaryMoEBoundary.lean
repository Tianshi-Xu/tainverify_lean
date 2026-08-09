/- Canonical Goal 1: ordinary K/V cache source boundary at SM 4990 and PM 7918/7919. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L0OrdinaryMoEDown
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

private def l0OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [4973, 4986], outs := [4987] }
private def l0OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [7862, 7898], outs := [7904] }
private def l0OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [7863, 7899], outs := [7905] }

private def l0OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [4968, 4987], outs := [4988] }
private def l0OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [7852, 7904], outs := [7908] }
private def l0OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [7853, 7905], outs := [7909] }

private def l0OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [4988], outs := [4989] }
private def l0OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [7908], outs := [7914] }
private def l0OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [7909], outs := [7915] }

private def l0OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [7769, 4989], outs := [4990] }
private def l0OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15458, 7914], outs := [7918] }
private def l0OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15466, 7915], outs := [7919] }

private theorem l0OMO_red_sm4987 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4987 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 4973)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 4986) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 37 l0OMOSmMul
    4973 4986 4987 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 4973 4986 4987

private theorem l0OMO_red_pm7904 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7904 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 7862)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 7898) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 108 l0OMOPmMul0
    7862 7898 7904 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 7862 7898 7904

private theorem l0OMO_red_pm7905 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7905 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 7863)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 7899) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 109 l0OMOPmMul1
    7863 7899 7905 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 7863 7899 7905

private theorem l0OMO_red_sm4988 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4988 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 4968)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 4987) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 38 l0OMOSmJoin
    4968 4987 4988 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 4968 4987 4988

private theorem l0OMO_red_pm7908 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7908 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 7852)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 7904) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 110 l0OMOPmJoin0
    7852 7904 7908 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 7852 7904 7908

private theorem l0OMO_red_pm7909 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7909 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 7853)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 7905) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 111 l0OMOPmJoin1
    7853 7905 7909 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 7853 7905 7909

private theorem l0OMO_red_sm4989 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4989 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 4988 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 39 l0OMOSmFloat
    4988 4989 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 4988 4989 []

private theorem l0OMO_red_pm7914 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7914 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7908 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 112 l0OMOPmFloat0
    7908 7914 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 7908 7914 []

private theorem l0OMO_red_pm7915 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7915 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7909 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 113 l0OMOPmFloat1
    7909 7915 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 7909 7915 []

private theorem l0OMO_red_sm4990 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4990 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 7769)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 4989) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 40 l0OMOSmOutput
    7769 4989 4990 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 7769 4989 4990

private theorem l0OMO_red_pm7918 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7918 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15458)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 7914) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 114 l0OMOPmOutput0
    15458 7914 7918 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15458 7914 7918

private theorem l0OMO_red_pm7919 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7919 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15466)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 7915) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 115 l0OMOPmOutput1
    15466 7915 7919 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15466 7915 7919



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
theorem l0_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7769)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15458)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15466)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7852)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7853)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7862)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7863)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4986)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7898)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7899)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7918)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7919)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4987)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7905)
      [4096, 1024] [2048, 1024] := by
    rw [l0OMO_red_sm4987 initSM, l0OMO_red_pm7904 initPM, l0OMO_red_pm7905 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4988)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7908)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7909)
      [4096, 1024] [2048, 1024] := by
    rw [l0OMO_red_sm4988 initSM, l0OMO_red_pm7908 initPM, l0OMO_red_pm7909 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4989)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7914)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7915)
      [4096, 1024] [2048, 1024] := by
    rw [l0OMO_red_sm4989 initSM, l0OMO_red_pm7914 initPM, l0OMO_red_pm7915 initPM]
    exact hJoin
  rw [l0OMO_red_sm4990 initSM, l0OMO_red_pm7918 initPM, l0OMO_red_pm7919 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l0_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
