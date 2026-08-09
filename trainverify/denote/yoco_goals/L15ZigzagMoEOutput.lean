/- Canonical Goal 1, layer 15: faithful MoE join and residual output. -/
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

private def l15ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5906, 5919], outs := [5920] }
private def l15ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10618, 10654], outs := [10660] }
private def l15ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10619, 10655], outs := [10661] }

private def l15ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5901, 5920], outs := [5921] }
private def l15ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10608, 10660], outs := [10664] }
private def l15ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10609, 10661], outs := [10665] }

private def l15ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5921], outs := [5922] }
private def l15ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10664], outs := [10670] }
private def l15ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10665], outs := [10671] }

private def l15ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8707, 5922], outs := [5923] }
private def l15ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16266, 10670], outs := [10674] }
private def l15ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16274, 10671], outs := [10675] }

private theorem l15ZMo_red_sm5920 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5920 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5906)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5919) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 708 l15ZMoSmMul
    5906 5919 5920 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5906 5919 5920

private theorem l15ZMo_red_pm10660 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10660 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10618)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10654) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1552 l15ZMoPmMul0
    10618 10654 10660 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 10618 10654 10660

private theorem l15ZMo_red_pm10661 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10661 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10619)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10655) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1553 l15ZMoPmMul1
    10619 10655 10661 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 10619 10655 10661

private theorem l15ZMo_red_sm5921 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5921 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5901)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5920) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 709 l15ZMoSmJoin
    5901 5920 5921 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5901 5920 5921

private theorem l15ZMo_red_pm10664 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10664 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10608)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10660) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1554 l15ZMoPmJoin0
    10608 10660 10664 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 10608 10660 10664

private theorem l15ZMo_red_pm10665 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10665 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10609)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10661) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1555 l15ZMoPmJoin1
    10609 10661 10665 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 10609 10661 10665

private theorem l15ZMo_red_sm5922 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5922 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5921 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 710 l15ZMoSmFloat
    5921 5922 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5921 5922 []

private theorem l15ZMo_red_pm10670 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10670 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10664 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1556 l15ZMoPmFloat0
    10664 10670 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10664 10670 []

private theorem l15ZMo_red_pm10671 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10671 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10665 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1557 l15ZMoPmFloat1
    10665 10671 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10665 10671 []

private theorem l15ZMo_red_sm5923 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5923 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8707)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5922) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 711 l15ZMoSmOutput
    8707 5922 5923 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8707 5922 5923

private theorem l15ZMo_red_pm10674 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10674 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16266)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10670) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1558 l15ZMoPmOutput0
    16266 10670 10674 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16266 10670 10674

private theorem l15ZMo_red_pm10675 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10675 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16274)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10671) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1559 l15ZMoPmOutput1
    16274 10671 10675 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16274 10671 10675

/-- The real canonical L15 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `5923 ↔ 10674/10675` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem l15_zigzag_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8707)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16266)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16274)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5901)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10608)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10609)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5906)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10618)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10619)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5919)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10654)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10655)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5923)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10675)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5906)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10618)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10619)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5919)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10654)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10655)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5920)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10660)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10661)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMo_red_sm5920 initSM, l15ZMo_red_pm10660 initPM,
      l15ZMo_red_pm10661 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5921)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10664)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10665)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMo_red_sm5921 initSM, l15ZMo_red_pm10664 initPM,
      l15ZMo_red_pm10665 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5922)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10670)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10671)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMo_red_sm5922 initSM, l15ZMo_red_pm10670 initPM,
      l15ZMo_red_pm10671 initPM]
    exact hJoin
  rw [l15ZMo_red_sm5923 initSM, l15ZMo_red_pm10674 initPM,
    l15ZMo_red_pm10675 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
