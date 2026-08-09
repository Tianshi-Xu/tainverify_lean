/- Canonical Goal 1, layer 18: faithful MoE join and residual output. -/
import denote.yoco_goals.Goal_1
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

private def l18ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [6068, 6081], outs := [6082] }
private def l18ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [11080, 11116], outs := [11122] }
private def l18ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [11081, 11117], outs := [11123] }

private def l18ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [6063, 6082], outs := [6083] }
private def l18ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [11070, 11122], outs := [11126] }
private def l18ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [11071, 11123], outs := [11127] }

private def l18ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [6083], outs := [6084] }
private def l18ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11126], outs := [11132] }
private def l18ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11127], outs := [11133] }

private def l18ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8824, 6084], outs := [6085] }
private def l18ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16362, 11132], outs := [11136] }
private def l18ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16370, 11133], outs := [11137] }

private theorem l18ZMo_red_sm6082 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6082 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 6068)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6081) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 813 l18ZMoSmMul
    6068 6081 6082 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 6068 6081 6082

private theorem l18ZMo_red_pm11122 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11122 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 11080)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11116) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1780 l18ZMoPmMul0
    11080 11116 11122 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 11080 11116 11122

private theorem l18ZMo_red_pm11123 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11123 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 11081)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11117) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1781 l18ZMoPmMul1
    11081 11117 11123 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 11081 11117 11123

private theorem l18ZMo_red_sm6083 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6083 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 6063)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6082) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 814 l18ZMoSmJoin
    6063 6082 6083 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 6063 6082 6083

private theorem l18ZMo_red_pm11126 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11126 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 11070)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11122) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1782 l18ZMoPmJoin0
    11070 11122 11126 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 11070 11122 11126

private theorem l18ZMo_red_pm11127 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11127 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 11071)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11123) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1783 l18ZMoPmJoin1
    11071 11123 11127 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 11071 11123 11127

private theorem l18ZMo_red_sm6084 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6084 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6083 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 815 l18ZMoSmFloat
    6083 6084 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 6083 6084 []

private theorem l18ZMo_red_pm11132 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11132 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11126 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1784 l18ZMoPmFloat0
    11126 11132 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 11126 11132 []

private theorem l18ZMo_red_pm11133 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11133 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11127 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1785 l18ZMoPmFloat1
    11127 11133 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11127 11133 []

private theorem l18ZMo_red_sm6085 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6085 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8824)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6084) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 816 l18ZMoSmOutput
    8824 6084 6085 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8824 6084 6085

private theorem l18ZMo_red_pm11136 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11136 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16362)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11132) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1786 l18ZMoPmOutput0
    16362 11132 11136 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16362 11132 11136

private theorem l18ZMo_red_pm11137 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11137 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16370)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11133) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1787 l18ZMoPmOutput1
    16370 11133 11137 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16370 11133 11137

/-- The real canonical L18 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `6085 ↔ 11136/11137` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem l18_zigzag_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8824)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16362)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16370)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6063)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11070)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11071)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6068)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11080)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11081)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6081)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11116)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11117)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6085)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11136)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11137)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6068)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11080)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11081)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6081)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11116)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11117)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6082)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMo_red_sm6082 initSM, l18ZMo_red_pm11122 initPM,
      l18ZMo_red_pm11123 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6083)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11126)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11127)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMo_red_sm6083 initSM, l18ZMo_red_pm11126 initPM,
      l18ZMo_red_pm11127 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6084)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11132)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11133)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMo_red_sm6084 initSM, l18ZMo_red_pm11132 initPM,
      l18ZMo_red_pm11133 initPM]
    exact hJoin
  rw [l18ZMo_red_sm6085 initSM, l18ZMo_red_pm11136 initPM,
    l18ZMo_red_pm11137 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
