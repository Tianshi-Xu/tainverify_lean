/- Canonical Goal 1, layer 12: faithful MoE join and residual output. -/
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

private def l12ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5636, 5649], outs := [5650] }
private def l12ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [9848, 9884], outs := [9890] }
private def l12ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [9849, 9885], outs := [9891] }

private def l12ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5631, 5650], outs := [5651] }
private def l12ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9838, 9890], outs := [9894] }
private def l12ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9839, 9891], outs := [9895] }

private def l12ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5651], outs := [5652] }
private def l12ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9894], outs := [9900] }
private def l12ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9895], outs := [9901] }

private def l12ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8512, 5652], outs := [5653] }
private def l12ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16106, 9900], outs := [9904] }
private def l12ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16114, 9901], outs := [9905] }

private theorem l12ZMo_red_sm5650 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5650 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5636)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5649) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 533 l12ZMoSmMul
    5636 5649 5650 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5636 5649 5650

private theorem l12ZMo_red_pm9890 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9890 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9848)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9884) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1172 l12ZMoPmMul0
    9848 9884 9890 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 9848 9884 9890

private theorem l12ZMo_red_pm9891 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9891 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 9849)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9885) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1173 l12ZMoPmMul1
    9849 9885 9891 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 9849 9885 9891

private theorem l12ZMo_red_sm5651 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5651 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5631)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5650) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 534 l12ZMoSmJoin
    5631 5650 5651 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5631 5650 5651

private theorem l12ZMo_red_pm9894 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9894 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9838)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9890) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1174 l12ZMoPmJoin0
    9838 9890 9894 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 9838 9890 9894

private theorem l12ZMo_red_pm9895 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9895 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 9839)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9891) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1175 l12ZMoPmJoin1
    9839 9891 9895 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 9839 9891 9895

private theorem l12ZMo_red_sm5652 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5652 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5651 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 535 l12ZMoSmFloat
    5651 5652 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5651 5652 []

private theorem l12ZMo_red_pm9900 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9900 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9894 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1176 l12ZMoPmFloat0
    9894 9900 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9894 9900 []

private theorem l12ZMo_red_pm9901 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9901 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9895 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1177 l12ZMoPmFloat1
    9895 9901 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9895 9901 []

private theorem l12ZMo_red_sm5653 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5653 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8512)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5652) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 536 l12ZMoSmOutput
    8512 5652 5653 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8512 5652 5653

private theorem l12ZMo_red_pm9904 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9904 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16106)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9900) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1178 l12ZMoPmOutput0
    16106 9900 9904 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16106 9900 9904

private theorem l12ZMo_red_pm9905 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9905 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16114)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9901) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1179 l12ZMoPmOutput1
    16114 9901 9905 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16114 9901 9905

/-- The real canonical L21 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `5653 ↔ 9904/9905` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem l12_zigzag_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16114)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5631)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9838)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9839)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9848)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9849)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5649)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9885)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9905)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9848)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9849)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5649)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9885)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5650)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9891)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMo_red_sm5650 initSM, l12ZMo_red_pm9890 initPM,
      l12ZMo_red_pm9891 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5651)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9894)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9895)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMo_red_sm5651 initSM, l12ZMo_red_pm9894 initPM,
      l12ZMo_red_pm9895 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5652)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9900)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9901)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMo_red_sm5652 initSM, l12ZMo_red_pm9900 initPM,
      l12ZMo_red_pm9901 initPM]
    exact hJoin
  rw [l12ZMo_red_sm5653 initSM, l12ZMo_red_pm9904 initPM,
    l12ZMo_red_pm9905 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
