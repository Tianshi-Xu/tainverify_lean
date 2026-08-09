/- Canonical Goal 1, layer 19: faithful attention projection and residual output. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagLinearRel
import denote.yoco_goals.ZigzagPointwiseRel
import denote.yoco_goals.ZigzagViewRel

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

private def cL19SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6098], outs := [6100],
    params := [4096, 1024] }
private def cL19SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6100], outs := [6101],
    params := [4096, 1024] }
private def cL19SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6101, 6102],
    outs := [6103] }
private def cL19SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6103], outs := [6104],
    params := [4096, 1024] }
private def cL19SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [6104], outs := [6105] }
private def cL19SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8855, 6105], outs := [6106] }

private def cL19PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11170], outs := [11172],
    params := [2048, 1024] }
private def cL19PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11171], outs := [11173],
    params := [2048, 1024] }
private def cL19PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11172], outs := [11178],
    params := [2048, 1024] }
private def cL19PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11173], outs := [11179],
    params := [2048, 1024] }
private def cL19PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11178, 6102],
    outs := [11182] }
private def cL19PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11179, 6102],
    outs := [11183] }
private def cL19PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11182], outs := [11192],
    params := [2048, 1024] }
private def cL19PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11183], outs := [11193],
    params := [2048, 1024] }
private def cL19PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11192], outs := [11196] }
private def cL19PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11193], outs := [11197] }
private def cL19PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16378, 11196], outs := [11200] }
private def cL19PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16386, 11197], outs := [11201] }

private theorem cL19_red_sm5776 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6100 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6098) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 821 cL19SmReshape0
    6098 6100 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6098 6100 [4096, 1024]

private theorem cL19_red_pm10248 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11172 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11170) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1799 cL19PmReshape0
    11170 11172 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19PmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11170 11172 [2048, 1024]

private theorem cL19_red_pm10249 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11173 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11171) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1800 cL19PmReshape1
    11171 11173 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19PmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11171 11173 [2048, 1024]

private theorem cL19_red_sm5777 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6101 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6100) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 822 cL19SmReshape1
    6100 6101 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6100 6101 [4096, 1024]

private theorem cL19_red_pm10254 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11178 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11172) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1801 cL19PmReshape10
    11172 11178 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11172 11178 [2048, 1024]

private theorem cL19_red_pm10255 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11179 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11173) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1802 cL19PmReshape11
    11173 11179 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11173 11179 [2048, 1024]

private theorem cL19_red_sm5779 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6103 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6101)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6102) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 823 cL19SmLinear
    6101 6102 6103 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL19SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6101 6102 6103

private theorem cL19_red_pm10258 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11182 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11178)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6102) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1803 cL19PmLinear0
    11178 6102 11182 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL19PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11178 6102 11182

private theorem cL19_red_pm10259 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11183 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11179)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6102) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1804 cL19PmLinear1
    11179 6102 11183 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL19PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11179 6102 11183

private theorem cL19_red_sm5780 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6104 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6103) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 824 cL19SmView
    6103 6104 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 6103 6104

private theorem cL19_red_pm10268 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11192 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11182) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1805 cL19PmView0
    11182 11192 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 11182 11192

private theorem cL19_red_pm10269 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11193 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11183) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1806 cL19PmView1
    11183 11193 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 11183 11193

private theorem cL19_red_sm5781 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6105 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6104 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 825 cL19SmFloat
    6104 6105 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 6104 6105 []

private theorem cL19_red_pm10272 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11196 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11192 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1807 cL19PmFloat0
    11192 11196 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 11192 11196 []

private theorem cL19_red_pm10273 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11197 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11193 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1808 cL19PmFloat1
    11193 11197 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11193 11197 []

private theorem cL19_red_sm5782 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6106 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8855)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6105) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 826 cL19SmAdd
    8855 6105 6106 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL19SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8855 6105 6106

private theorem cL19_red_pm10276 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11200 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16378)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11196) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1809 cL19PmAdd0
    16378 11196 11200 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL19PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16378 11196 11200

private theorem cL19_red_pm10277 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11201 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16386)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11197) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1810 cL19PmAdd1
    16386 11197 11201 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL19PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16386 11197 11201

/-- The real canonical L19 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l19_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6098)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11170)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11171)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6102 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6102)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6102).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6105)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11196)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11197)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11172)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11173)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL19_red_sm5776 initSM, cL19_red_pm10248 initPM, cL19_red_pm10249 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6101)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11178)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11179)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL19_red_sm5777 initSM, cL19_red_pm10254 initPM, cL19_red_pm10255 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6103)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11182)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11183)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL19_red_sm5779 initSM, cL19_red_pm10258 initPM, cL19_red_pm10259 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6104)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11192)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL19_red_sm5780 initSM, cL19_red_pm10268 initPM, cL19_red_pm10269 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL19_red_sm5781 initSM, cL19_red_pm10272 initPM, cL19_red_pm10273 initPM]
  exact hView

/-- Canonical L19 output relation at the exact values consumed by the L19 MoE tail.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `6106 ↔ 11200/11201` relation is a conclusion, never a
caller contract. -/
theorem canonical_l19_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8855)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16378)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16386)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6098)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11170)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11171)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6102 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6102)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6102).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l19_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL19_red_sm5782 initSM, cL19_red_pm10276 initPM, cL19_red_pm10277 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l19_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
