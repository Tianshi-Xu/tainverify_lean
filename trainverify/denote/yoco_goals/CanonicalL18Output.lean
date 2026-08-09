/- Canonical Goal 1, layer 18: faithful attention projection and residual output. -/
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

private def cL18SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6044], outs := [6046],
    params := [4096, 1024] }
private def cL18SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6046], outs := [6047],
    params := [4096, 1024] }
private def cL18SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6047, 6048],
    outs := [6049] }
private def cL18SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6049], outs := [6050],
    params := [4096, 1024] }
private def cL18SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [6050], outs := [6051] }
private def cL18SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8816, 6051], outs := [6052] }

private def cL18PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11016], outs := [11018],
    params := [2048, 1024] }
private def cL18PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11017], outs := [11019],
    params := [2048, 1024] }
private def cL18PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11018], outs := [11024],
    params := [2048, 1024] }
private def cL18PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11019], outs := [11025],
    params := [2048, 1024] }
private def cL18PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11024, 6048],
    outs := [11028] }
private def cL18PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11025, 6048],
    outs := [11029] }
private def cL18PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11028], outs := [11038],
    params := [2048, 1024] }
private def cL18PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11029], outs := [11039],
    params := [2048, 1024] }
private def cL18PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11038], outs := [11042] }
private def cL18PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11039], outs := [11043] }
private def cL18PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16346, 11042], outs := [11046] }
private def cL18PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16354, 11043], outs := [11047] }

private theorem cL18_red_sm5776 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6046 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6044) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 786 cL18SmReshape0
    6044 6046 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6044 6046 [4096, 1024]

private theorem cL18_red_pm10248 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11018 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11016) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1723 cL18PmReshape0
    11016 11018 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18PmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11016 11018 [2048, 1024]

private theorem cL18_red_pm10249 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11019 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11017) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1724 cL18PmReshape1
    11017 11019 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18PmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11017 11019 [2048, 1024]

private theorem cL18_red_sm5777 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6047 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6046) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 787 cL18SmReshape1
    6046 6047 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6046 6047 [4096, 1024]

private theorem cL18_red_pm10254 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11024 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11018) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1725 cL18PmReshape10
    11018 11024 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11018 11024 [2048, 1024]

private theorem cL18_red_pm10255 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11025 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11019) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1726 cL18PmReshape11
    11019 11025 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11019 11025 [2048, 1024]

private theorem cL18_red_sm5779 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6049 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6047)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6048) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 788 cL18SmLinear
    6047 6048 6049 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL18SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6047 6048 6049

private theorem cL18_red_pm10258 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11028 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11024)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6048) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1727 cL18PmLinear0
    11024 6048 11028 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL18PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11024 6048 11028

private theorem cL18_red_pm10259 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11029 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11025)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6048) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1728 cL18PmLinear1
    11025 6048 11029 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL18PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11025 6048 11029

private theorem cL18_red_sm5780 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6050 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6049) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 789 cL18SmView
    6049 6050 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 6049 6050

private theorem cL18_red_pm10268 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11038 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11028) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1729 cL18PmView0
    11028 11038 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 11028 11038

private theorem cL18_red_pm10269 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11039 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11029) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1730 cL18PmView1
    11029 11039 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 11029 11039

private theorem cL18_red_sm5781 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6051 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6050 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 790 cL18SmFloat
    6050 6051 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 6050 6051 []

private theorem cL18_red_pm10272 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11042 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11038 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1731 cL18PmFloat0
    11038 11042 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 11038 11042 []

private theorem cL18_red_pm10273 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11043 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11039 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1732 cL18PmFloat1
    11039 11043 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11039 11043 []

private theorem cL18_red_sm5782 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6052 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8816)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6051) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 791 cL18SmAdd
    8816 6051 6052 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL18SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8816 6051 6052

private theorem cL18_red_pm10276 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11046 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16346)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11042) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1733 cL18PmAdd0
    16346 11042 11046 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL18PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16346 11042 11046

private theorem cL18_red_pm10277 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11047 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16354)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11043) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1734 cL18PmAdd1
    16354 11043 11047 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL18PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16354 11043 11047

/-- The real canonical L18 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l18_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6044)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11016)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11017)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6048 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6048)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6048).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6051)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11042)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11043)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11018)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11019)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL18_red_sm5776 initSM, cL18_red_pm10248 initPM, cL18_red_pm10249 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11024)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11025)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL18_red_sm5777 initSM, cL18_red_pm10254 initPM, cL18_red_pm10255 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6049)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11028)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11029)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL18_red_sm5779 initSM, cL18_red_pm10258 initPM, cL18_red_pm10259 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11038)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11039)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL18_red_sm5780 initSM, cL18_red_pm10268 initPM, cL18_red_pm10269 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL18_red_sm5781 initSM, cL18_red_pm10272 initPM, cL18_red_pm10273 initPM]
  exact hView

/-- Canonical L18 output relation at the exact values consumed by the L18 MoE tail.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `6052 ↔ 11046/11047` relation is a conclusion, never a
caller contract. -/
theorem canonical_l18_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8816)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16346)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6044)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11016)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11017)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6048 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6048)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6048).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l18_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL18_red_sm5782 initSM, cL18_red_pm10276 initPM, cL18_red_pm10277 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l18_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
