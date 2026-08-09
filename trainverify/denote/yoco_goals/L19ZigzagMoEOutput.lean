/- Canonical Goal 1, layer 19: faithful MoE join and residual output. -/
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

private def l19ZMoSmMul : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [6122, 6135], outs := [6136] }
private def l19ZMoPmMul0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [11234, 11270], outs := [11276] }
private def l19ZMoPmMul1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [11235, 11271], outs := [11277] }

private def l19ZMoSmJoin : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [6117, 6136], outs := [6137] }
private def l19ZMoPmJoin0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [11224, 11276], outs := [11280] }
private def l19ZMoPmJoin1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [11225, 11277], outs := [11281] }

private def l19ZMoSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [6137], outs := [6138] }
private def l19ZMoPmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11280], outs := [11286] }
private def l19ZMoPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11281], outs := [11287] }

private def l19ZMoSmOutput : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8863, 6138], outs := [6139] }
private def l19ZMoPmOutput0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16394, 11286], outs := [11290] }
private def l19ZMoPmOutput1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16402, 11287], outs := [11291] }

private theorem l19ZMo_red_sm6136 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6136 =
      elemwiseMul (denoteGraphDistributedFaithful sm_goal_1 initSM 6122)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6135) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 848 l19ZMoSmMul
    6122 6135 6136 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoSmMul
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm_goal_1 s 0 6122 6135 6136

private theorem l19ZMo_red_pm11276 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11276 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 11234)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11270) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1856 l19ZMoPmMul0
    11234 11270 11276 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoPmMul0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 0 11234 11270 11276

private theorem l19ZMo_red_pm11277 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11277 =
      elemwiseMul (denoteGraphDistributedFaithful pm_goal_1 initPM 11235)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11271) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1857 l19ZMoPmMul1
    11235 11271 11277 elemwiseMul
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoPmMul1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm_goal_1 s 1 11235 11271 11277

private theorem l19ZMo_red_sm6137 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6137 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 6117)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6136) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 849 l19ZMoSmJoin
    6117 6136 6137 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoSmJoin
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 6117 6136 6137

private theorem l19ZMo_red_pm11280 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11280 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 11224)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11276) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1858 l19ZMoPmJoin0
    11224 11276 11280 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoPmJoin0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 11224 11276 11280

private theorem l19ZMo_red_pm11281 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11281 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 11225)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11277) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1859 l19ZMoPmJoin1
    11225 11277 11281 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoPmJoin1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 11225 11277 11281

private theorem l19ZMo_red_sm6138 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6138 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6137 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 850 l19ZMoSmFloat
    6137 6138 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 6137 6138 []

private theorem l19ZMo_red_pm11286 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11286 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11280 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1860 l19ZMoPmFloat0
    11280 11286 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoPmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 11280 11286 []

private theorem l19ZMo_red_pm11287 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11287 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11281 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1861 l19ZMoPmFloat1
    11281 11287 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11281 11287 []

private theorem l19ZMo_red_sm6139 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6139 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8863)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6138) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 851 l19ZMoSmOutput
    8863 6138 6139 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoSmOutput
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8863 6138 6139

private theorem l19ZMo_red_pm11290 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11290 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16394)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11286) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1862 l19ZMoPmOutput0
    16394 11286 11290 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoPmOutput0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16394 11286 11290

private theorem l19ZMo_red_pm11291 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11291 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16402)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11287) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1863 l19ZMoPmOutput1
    16402 11287 11291 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMoPmOutput1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16402 11287 11291

/-- The real canonical L19 tail (broadcast gate, MoE join, float, and residual
add) establishes exactly the `6139 ↔ 11290/11291` relation consumed by L22.
Every computed value in this segment is a conclusion; the premises are the four
independently composable upstream relations. -/
theorem l19_zigzag_moe_output_from_branch_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8863)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16394)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16402)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hExpert : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6117)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11224)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11225)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hGate : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11235)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1])
    (hDown : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6135)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11270)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11271)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6139)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11290)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11291)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  obtain ⟨g0, g1, hgs⟩ := hGate
  obtain ⟨d0, d1, hds⟩ := hDown
  have hGate' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11235)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨g0, g1, hgs⟩
  have hDown' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6135)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11270)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11271)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨d0, d1, hds⟩
  have hMul : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6136)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11277)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMo_red_sm6136 initSM, l19ZMo_red_pm11276 initPM,
      l19ZMo_red_pm11277 initPM]
    exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hGate' hDown'
      (by decide) (by decide)
  have hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6137)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11280)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11281)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMo_red_sm6137 initSM, l19ZMo_red_pm11280 initPM,
      l19ZMo_red_pm11281 initPM]
    exact Zigzag2Rel.add 2048 1024 hExpert hMul (by decide) (by decide)
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6138)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11286)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11287)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMo_red_sm6138 initSM, l19ZMo_red_pm11286 initPM,
      l19ZMo_red_pm11287 initPM]
    exact hJoin
  rw [l19ZMo_red_sm6139 initSM, l19ZMo_red_pm11290 initPM,
    l19ZMo_red_pm11291 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
