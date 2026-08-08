/- Canonical Goal 1, layer 22: faithful attention projection and residual output. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagLinearRel
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

private def cL22SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6206], outs := [6208],
    params := [4096, 1024] }
private def cL22SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6208], outs := [6209],
    params := [4096, 1024] }
private def cL22SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6209, 6210],
    outs := [6211] }
private def cL22SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6211], outs := [6212],
    params := [4096, 1024] }
private def cL22SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [6212], outs := [6213] }
private def cL22SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8933, 6213], outs := [6214] }

private def cL22PmReshape00 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11478], outs := [11480],
    params := [2048, 1024] }
private def cL22PmReshape01 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11479], outs := [11481],
    params := [2048, 1024] }
private def cL22PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11480], outs := [11486],
    params := [2048, 1024] }
private def cL22PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11481], outs := [11487],
    params := [2048, 1024] }
private def cL22PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11486, 6210],
    outs := [11490] }
private def cL22PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11487, 6210],
    outs := [11491] }
private def cL22PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11490], outs := [11500],
    params := [2048, 1024] }
private def cL22PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11491], outs := [11501],
    params := [2048, 1024] }
private def cL22PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11500], outs := [11504] }
private def cL22PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11501], outs := [11505] }
private def cL22PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16442, 11504], outs := [11508] }
private def cL22PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16450, 11505], outs := [11509] }

private theorem cL22_red_sm6208 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6208 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6206) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 891 cL22SmReshape0
    6206 6208 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6206 6208 [4096, 1024]

private theorem cL22_red_pm11480 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11480 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11478) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1951 cL22PmReshape00
    11478 11480 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22PmReshape00
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11478 11480 [2048, 1024]

private theorem cL22_red_pm11481 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11481 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11479) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1952 cL22PmReshape01
    11479 11481 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22PmReshape01
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11479 11481 [2048, 1024]

private theorem cL22_red_sm6209 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6209 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6208) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 892 cL22SmReshape1
    6208 6209 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6208 6209 [4096, 1024]

private theorem cL22_red_pm11486 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11486 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11480) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1953 cL22PmReshape10
    11480 11486 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11480 11486 [2048, 1024]

private theorem cL22_red_pm11487 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11487 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11481) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1954 cL22PmReshape11
    11481 11487 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11481 11487 [2048, 1024]

private theorem cL22_red_sm6211 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6211 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6209)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6210) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 893 cL22SmLinear
    6209 6210 6211 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL22SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6209 6210 6211

private theorem cL22_red_pm11490 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11490 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11486)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6210) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1955 cL22PmLinear0
    11486 6210 11490 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL22PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11486 6210 11490

private theorem cL22_red_pm11491 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11491 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11487)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6210) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1956 cL22PmLinear1
    11487 6210 11491 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL22PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11487 6210 11491

private theorem cL22_red_sm6212 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6212 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 6211) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 894 cL22SmView
    6211 6212 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 6211 6212

private theorem cL22_red_pm11500 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11500 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11490) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1957 cL22PmView0
    11490 11500 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 11490 11500

private theorem cL22_red_pm11501 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11501 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 11491) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1958 cL22PmView1
    11491 11501 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 11491 11501

private theorem cL22_red_sm6213 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6213 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6212 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 895 cL22SmFloat
    6212 6213 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 6212 6213 []

private theorem cL22_red_pm11504 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11504 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11500 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1959 cL22PmFloat0
    11500 11504 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 11500 11504 []

private theorem cL22_red_pm11505 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11505 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11501 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1960 cL22PmFloat1
    11501 11505 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11501 11505 []

private theorem cL22_red_sm6214 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6214 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8933)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6213) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 896 cL22SmAdd
    8933 6213 6214 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL22SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8933 6213 6214

private theorem cL22_red_pm11508 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11508 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16442)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11504) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1961 cL22PmAdd0
    16442 11504 11508 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL22PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16442 11504 11508

private theorem cL22_red_pm11509 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11509 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16450)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11505) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1962 cL22PmAdd1
    16450 11505 11509 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL22PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16450 11505 11509

/-- The real canonical L22 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l22_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6210 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6210)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6210).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6213)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11504)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11505)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6208)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11480)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11481)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL22_red_sm6208 initSM, cL22_red_pm11480 initPM, cL22_red_pm11481 initPM]
    exact Zigzag2Rel.view_id' hAttention
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6209)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11486)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11487)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL22_red_sm6209 initSM, cL22_red_pm11486 initPM, cL22_red_pm11487 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6211)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11490)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11491)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL22_red_sm6211 initSM, cL22_red_pm11490 initPM, cL22_red_pm11491 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6212)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11500)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11501)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL22_red_sm6212 initSM, cL22_red_pm11500 initPM, cL22_red_pm11501 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL22_red_sm6213 initSM, cL22_red_pm11504 initPM, cL22_red_pm11505 initPM]
  exact hView

/-- Canonical L22 output relation at the exact values consumed by L23.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `6214 ↔ 11508/11509` relation is a conclusion, never a
caller contract. -/
theorem canonical_l22_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16442)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16450)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 6210 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6210)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6210).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6214)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11508)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11509)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l22_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL22_red_sm6214 initSM, cL22_red_pm11508 initPM, cL22_red_pm11509 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
