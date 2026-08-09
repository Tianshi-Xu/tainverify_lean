/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5045 and PM 8082/8083. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L1OrdinaryMoEDown
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

private def l1OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5028, 5041], outs := [5042] }
private def l1OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [8026, 8062], outs := [8068] }
private def l1OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [8027, 8063], outs := [8069] }

private def l1OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5023, 5042], outs := [5043] }
private def l1OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8016, 8068], outs := [8072] }
private def l1OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [8017, 8069], outs := [8073] }

private def l1OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5043], outs := [5044] }
private def l1OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8072], outs := [8078] }
private def l1OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [8073], outs := [8079] }

private def l1OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [7821, 5044], outs := [5045] }
private def l1OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15490, 8078], outs := [8082] }
private def l1OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15498, 8079], outs := [8083] }

private theorem l1OMO_red_sm5042 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5042 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5028)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5041) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 76 l1OMOSmMul
    5028 5041 5042 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5028 5041 5042

private theorem l1OMO_red_pm8068 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8068 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8026)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8062) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 192 l1OMOPmMul0
    8026 8062 8068 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 8026 8062 8068

private theorem l1OMO_red_pm8069 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8069 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 8027)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8063) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 193 l1OMOPmMul1
    8027 8063 8069 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 8027 8063 8069

private theorem l1OMO_red_sm5043 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5043 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5023)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5042) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 77 l1OMOSmJoin
    5023 5042 5043 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5023 5042 5043

private theorem l1OMO_red_pm8072 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8072 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8016)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8068) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 194 l1OMOPmJoin0
    8016 8068 8072 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 8016 8068 8072

private theorem l1OMO_red_pm8073 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8073 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 8017)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8069) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 195 l1OMOPmJoin1
    8017 8069 8073 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 8017 8069 8073

private theorem l1OMO_red_sm5044 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5044 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5043 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 78 l1OMOSmFloat
    5043 5044 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5043 5044 []

private theorem l1OMO_red_pm8078 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8078 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8072 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 196 l1OMOPmFloat0
    8072 8078 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 8072 8078 []

private theorem l1OMO_red_pm8079 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8079 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8073 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 197 l1OMOPmFloat1
    8073 8079 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 8073 8079 []

private theorem l1OMO_red_sm5045 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5045 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 7821)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5044) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 79 l1OMOSmOutput
    7821 5044 5045 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 7821 5044 5045

private theorem l1OMO_red_pm8082 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8082 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15490)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8078) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 198 l1OMOPmOutput0
    15490 8078 8082 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 15490 8078 8082

private theorem l1OMO_red_pm8083 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8083 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 15498)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8079) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 199 l1OMOPmOutput1
    15498 8079 8083 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 15498 8079 8083



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
theorem l1_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7821)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15490)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15498)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5023)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8016)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8017)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5028)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8026)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8027)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5041)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8062)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8063)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5045)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8082)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8083)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5042)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8068)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8069)
      [4096, 1024] [2048, 1024] := by
    rw [l1OMO_red_sm5042 initSM, l1OMO_red_pm8068 initPM, l1OMO_red_pm8069 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5043)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8072)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8073)
      [4096, 1024] [2048, 1024] := by
    rw [l1OMO_red_sm5043 initSM, l1OMO_red_pm8072 initPM, l1OMO_red_pm8073 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5044)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8078)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8079)
      [4096, 1024] [2048, 1024] := by
    rw [l1OMO_red_sm5044 initSM, l1OMO_red_pm8078 initPM, l1OMO_red_pm8079 initPM]
    exact hJoin
  rw [l1OMO_red_sm5045 initSM, l1OMO_red_pm8082 initPM, l1OMO_red_pm8083 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l1_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
