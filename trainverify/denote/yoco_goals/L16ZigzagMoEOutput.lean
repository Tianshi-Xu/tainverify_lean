/- Canonical Goal 1, layer 16: faithful MoE join and residual output. -/
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

private def l16ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5960, 5973], outs := [5974] }
private def l16ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10772, 10808], outs := [10814] }
private def l16ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10773, 10809], outs := [10815] }

private def l16ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5955, 5974], outs := [5975] }
private def l16ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10762, 10814], outs := [10818] }
private def l16ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10763, 10815], outs := [10819] }

private def l16ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5975], outs := [5976] }
private def l16ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10818], outs := [10824] }
private def l16ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10819], outs := [10825] }

private def l16ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8746, 5976], outs := [5977] }
private def l16ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16298, 10824], outs := [10828] }
private def l16ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16306, 10825], outs := [10829] }

private theorem l16ZMo_red_sm5974 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5974 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5960)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5973) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 743 l16ZMoSmMul
    5960 5973 5974 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5960 5973 5974

private theorem l16ZMo_red_pm10814 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10814 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10772)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10808) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1628 l16ZMoPmMul0
    10772 10808 10814 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 10772 10808 10814

private theorem l16ZMo_red_pm10815 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10815 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10773)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10809) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1629 l16ZMoPmMul1
    10773 10809 10815 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 10773 10809 10815

private theorem l16ZMo_red_sm5975 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5975 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5955)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5974) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 744 l16ZMoSmJoin
    5955 5974 5975 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5955 5974 5975

private theorem l16ZMo_red_pm10818 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10818 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10762)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10814) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1630 l16ZMoPmJoin0
    10762 10814 10818 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 10762 10814 10818

private theorem l16ZMo_red_pm10819 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10819 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10763)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10815) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1631 l16ZMoPmJoin1
    10763 10815 10819 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 10763 10815 10819

private theorem l16ZMo_red_sm5976 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5976 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5975 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 745 l16ZMoSmFloat
    5975 5976 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5975 5976 []

private theorem l16ZMo_red_pm10824 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10824 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1632 l16ZMoPmFloat0
    10818 10824 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10818 10824 []

private theorem l16ZMo_red_pm10825 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10825 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1633 l16ZMoPmFloat1
    10819 10825 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10819 10825 []

private theorem l16ZMo_red_sm5977 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5977 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8746)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5976) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 746 l16ZMoSmOutput
    8746 5976 5977 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8746 5976 5977

private theorem l16ZMo_red_pm10828 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10828 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16298)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10824) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1634 l16ZMoPmOutput0
    16298 10824 10828 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16298 10824 10828

private theorem l16ZMo_red_pm10829 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10829 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16306)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10825) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1635 l16ZMoPmOutput1
    16306 10825 10829 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16306 10825 10829

/-- The real canonical L16 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `5977 ↔ 10828/10829` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem l16_zigzag_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8746)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16298)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16306)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5955)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10762)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10763)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5960)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10772)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10773)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10808)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10809)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10829)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5960)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10772)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10773)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10808)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10809)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5974)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10814)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10815)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMo_red_sm5974 initSM, l16ZMo_red_pm10814 initPM,
      l16ZMo_red_pm10815 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5975)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10819)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMo_red_sm5975 initSM, l16ZMo_red_pm10818 initPM,
      l16ZMo_red_pm10819 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5976)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10824)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10825)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMo_red_sm5976 initSM, l16ZMo_red_pm10824 initPM,
      l16ZMo_red_pm10825 initPM]
    exact hJoin
  rw [l16ZMo_red_sm5977 initSM, l16ZMo_red_pm10828 initPM,
    l16ZMo_red_pm10829 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
