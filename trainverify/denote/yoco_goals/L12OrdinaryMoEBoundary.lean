/- Canonical Goal 1: ordinary K/V cache source boundary at SM 5653 and PM 9904/9905. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.L12OrdinaryMoEDown
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

private def l12OMOSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5636, 5649], outs := [5650] }
private def l12OMOPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9848, 9884], outs := [9890] }
private def l12OMOPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9849, 9885], outs := [9891] }

private def l12OMOSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5631, 5650], outs := [5651] }
private def l12OMOPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9838, 9890], outs := [9894] }
private def l12OMOPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9839, 9891], outs := [9895] }

private def l12OMOSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5651], outs := [5652] }
private def l12OMOPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9894], outs := [9900] }
private def l12OMOPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9895], outs := [9901] }

private def l12OMOSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8512, 5652], outs := [5653] }
private def l12OMOPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16106, 9900], outs := [9904] }
private def l12OMOPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16114, 9901], outs := [9905] }

private theorem l12OMO_red_sm5650 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5650 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5636)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5649) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 533 l12OMOSmMul
    5636 5649 5650 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5636 5649 5650

private theorem l12OMO_red_pm9890 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9890 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9848)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9884) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1172 l12OMOPmMul0
    9848 9884 9890 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 9848 9884 9890

private theorem l12OMO_red_pm9891 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9891 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9849)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9885) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1173 l12OMOPmMul1
    9849 9885 9891 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 9849 9885 9891

private theorem l12OMO_red_sm5651 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5651 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5631)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5650) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 534 l12OMOSmJoin
    5631 5650 5651 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5631 5650 5651

private theorem l12OMO_red_pm9894 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9894 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9838)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9890) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1174 l12OMOPmJoin0
    9838 9890 9894 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 9838 9890 9894

private theorem l12OMO_red_pm9895 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9895 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9839)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9891) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1175 l12OMOPmJoin1
    9839 9891 9895 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 9839 9891 9895

private theorem l12OMO_red_sm5652 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5652 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5651 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 535 l12OMOSmFloat
    5651 5652 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5651 5652 []

private theorem l12OMO_red_pm9900 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9900 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9894 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1176 l12OMOPmFloat0
    9894 9900 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9894 9900 []

private theorem l12OMO_red_pm9901 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9901 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9895 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1177 l12OMOPmFloat1
    9895 9901 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9895 9901 []

private theorem l12OMO_red_sm5653 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5653 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8512)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5652) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 536 l12OMOSmOutput
    8512 5652 5653 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8512 5652 5653

private theorem l12OMO_red_pm9904 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9904 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16106)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9900) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1178 l12OMOPmOutput0
    16106 9900 9904 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16106 9900 9904

private theorem l12OMO_red_pm9905 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9905 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16114)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9901) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1179 l12OMOPmOutput1
    16114 9901 9905 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16114 9901 9905



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
theorem l12_ordinary_moe_boundary_from_branch_inputs (initSM initPM : Store)
    (hResidual : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16114)
      [4096, 1024] [2048, 1024])
    (hExpert : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5631)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9838)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9839)
      [4096, 1024] [2048, 1024])
    (hGate : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9848)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9849)
      [4096, 1] [2048, 1])
    (hDown : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5649)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9885)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9905)
      [4096, 1024] [2048, 1024] := by
  have hMul : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5650)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9891)
      [4096, 1024] [2048, 1024] := by
    rw [l12OMO_red_sm5650 initSM, l12OMO_red_pm9890 initPM, l12OMO_red_pm9891 initPM]
    exact ordinary_mul_broadcast 2048 1024 hGate hDown (by decide) (by decide)
  have hJoin : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5651)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9894)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9895)
      [4096, 1024] [2048, 1024] := by
    rw [l12OMO_red_sm5651 initSM, l12OMO_red_pm9894 initPM, l12OMO_red_pm9895 initPM]
    exact ordinary_add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5652)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9900)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9901)
      [4096, 1024] [2048, 1024] := by
    rw [l12OMO_red_sm5652 initSM, l12OMO_red_pm9900 initPM, l12OMO_red_pm9901 initPM]
    exact hJoin
  rw [l12OMO_red_sm5653 initSM, l12OMO_red_pm9904 initPM, l12OMO_red_pm9905 initPM]
  exact ordinary_add 2048 1024 hResidual hFloat (by decide) (by decide)

#print axioms l12_ordinary_moe_boundary_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
