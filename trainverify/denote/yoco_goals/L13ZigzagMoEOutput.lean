/- Canonical Goal 1, layer 13: faithful MoE join and residual output. -/
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

private def l13ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5798, 5811], outs := [5812] }
private def l13ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10310, 10346], outs := [10352] }
private def l13ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10311, 10347], outs := [10353] }

private def l13ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5793, 5812], outs := [5813] }
private def l13ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10300, 10352], outs := [10356] }
private def l13ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10301, 10353], outs := [10357] }

private def l13ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5813], outs := [5814] }
private def l13ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10356], outs := [10362] }
private def l13ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10357], outs := [10363] }

private def l13ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8629, 5814], outs := [5815] }
private def l13ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16202, 10362], outs := [10366] }
private def l13ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16210, 10363], outs := [10367] }

private theorem l13ZMo_red_sm5812 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5812 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 5798)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5811) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 638 l13ZMoSmMul
    5798 5811 5812 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 5798 5811 5812

private theorem l13ZMo_red_pm10352 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10352 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10310)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10346) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1400 l13ZMoPmMul0
    10310 10346 10352 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 10310 10346 10352

private theorem l13ZMo_red_pm10353 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10353 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 10311)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10347) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1401 l13ZMoPmMul1
    10311 10347 10353 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 10311 10347 10353

private theorem l13ZMo_red_sm5813 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5813 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 5793)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5812) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 639 l13ZMoSmJoin
    5793 5812 5813 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 5793 5812 5813

private theorem l13ZMo_red_pm10356 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10356 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10300)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10352) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1402 l13ZMoPmJoin0
    10300 10352 10356 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 10300 10352 10356

private theorem l13ZMo_red_pm10357 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10357 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 10301)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10353) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1403 l13ZMoPmJoin1
    10301 10353 10357 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 10301 10353 10357

private theorem l13ZMo_red_sm5814 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5814 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5813 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 640 l13ZMoSmFloat
    5813 5814 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5813 5814 []

private theorem l13ZMo_red_pm10362 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10362 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10356 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1404 l13ZMoPmFloat0
    10356 10362 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10356 10362 []

private theorem l13ZMo_red_pm10363 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10363 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10357 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1405 l13ZMoPmFloat1
    10357 10363 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10357 10363 []

private theorem l13ZMo_red_sm5815 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5815 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8629)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5814) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 641 l13ZMoSmOutput
    8629 5814 5815 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8629 5814 5815

private theorem l13ZMo_red_pm10366 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10366 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16202)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10362) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1406 l13ZMoPmOutput0
    16202 10362 10366 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16202 10362 10366

private theorem l13ZMo_red_pm10367 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10367 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16210)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10363) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1407 l13ZMoPmOutput1
    16210 10363 10367 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16210 10363 10367

/-- The real canonical L13 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `5815 ↔ 10366/10367` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem l13_zigzag_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8629)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5793)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10300)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10301)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5798)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10310)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10311)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5811)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10346)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10347)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5815)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10366)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10367)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5798)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10310)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10311)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5811)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10346)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10347)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10352)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10353)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMo_red_sm5812 initSM, l13ZMo_red_pm10352 initPM,
      l13ZMo_red_pm10353 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10356)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10357)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMo_red_sm5813 initSM, l13ZMo_red_pm10356 initPM,
      l13ZMo_red_pm10357 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5814)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10362)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10363)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMo_red_sm5814 initSM, l13ZMo_red_pm10362 initPM,
      l13ZMo_red_pm10363 initPM]
    exact hJoin
  rw [l13ZMo_red_sm5815 initSM, l13ZMo_red_pm10366 initPM,
    l13ZMo_red_pm10367 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
