/- Canonical Goal 1, layer 17: faithful MoE join and residual output. -/
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

private def l17ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [6014, 6027], outs := [6028] }
private def l17ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10926, 10962], outs := [10968] }
private def l17ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10927, 10963], outs := [10969] }

private def l17ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [6009, 6028], outs := [6029] }
private def l17ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10916, 10968], outs := [10972] }
private def l17ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10917, 10969], outs := [10973] }

private def l17ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [6029], outs := [6030] }
private def l17ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10972], outs := [10978] }
private def l17ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10973], outs := [10979] }

private def l17ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8785, 6030], outs := [6031] }
private def l17ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16330, 10978], outs := [10982] }
private def l17ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16338, 10979], outs := [10983] }

private theorem l17ZMo_red_sm6028 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6028 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 6014)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6027) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 778 l17ZMoSmMul
    6014 6027 6028 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 6014 6027 6028

private theorem l17ZMo_red_pm10968 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10968 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10926)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10962) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1704 l17ZMoPmMul0
    10926 10962 10968 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 10926 10962 10968

private theorem l17ZMo_red_pm10969 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10969 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10927)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10963) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1705 l17ZMoPmMul1
    10927 10963 10969 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 10927 10963 10969

private theorem l17ZMo_red_sm6029 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6029 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 6009)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6028) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 779 l17ZMoSmJoin
    6009 6028 6029 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 6009 6028 6029

private theorem l17ZMo_red_pm10972 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10972 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10916)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10968) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1706 l17ZMoPmJoin0
    10916 10968 10972 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 10916 10968 10972

private theorem l17ZMo_red_pm10973 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10973 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10917)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10969) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1707 l17ZMoPmJoin1
    10917 10969 10973 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 10917 10969 10973

private theorem l17ZMo_red_sm6030 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6030 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6029 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 780 l17ZMoSmFloat
    6029 6030 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 6029 6030 []

private theorem l17ZMo_red_pm10978 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10978 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10972 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1708 l17ZMoPmFloat0
    10972 10978 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10972 10978 []

private theorem l17ZMo_red_pm10979 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10979 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10973 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1709 l17ZMoPmFloat1
    10973 10979 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10973 10979 []

private theorem l17ZMo_red_sm6031 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6031 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8785)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6030) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 781 l17ZMoSmOutput
    8785 6030 6031 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8785 6030 6031

private theorem l17ZMo_red_pm10982 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10982 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16330)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10978) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1710 l17ZMoPmOutput0
    16330 10978 10982 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16330 10978 10982

private theorem l17ZMo_red_pm10983 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10983 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16338)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10979) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1711 l17ZMoPmOutput1
    16338 10979 10983 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16338 10979 10983

/-- The real canonical L17 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `6031 ↔ 10982/10983` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem l17_zigzag_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8785)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16330)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16338)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6009)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10916)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10917)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6014)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10926)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10927)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6027)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10962)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10963)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6031)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10982)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6014)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10926)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10927)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6027)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10962)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10963)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6028)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMo_red_sm6028 initSM, l17ZMo_red_pm10968 initPM,
      l17ZMo_red_pm10969 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6029)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10972)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMo_red_sm6029 initSM, l17ZMo_red_pm10972 initPM,
      l17ZMo_red_pm10973 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6030)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10978)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10979)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMo_red_sm6030 initSM, l17ZMo_red_pm10978 initPM,
      l17ZMo_red_pm10979 initPM]
    exact hJoin
  rw [l17ZMo_red_sm6031 initSM, l17ZMo_red_pm10982 initPM,
    l17ZMo_red_pm10983 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
