/- Canonical Goal 1, L12 block 3: faithful attention projection and residual output. -/
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

private def b3SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5720], outs := [5722],
    params := [4096, 1024] }
private def b3SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5722], outs := [5723],
    params := [4096, 1024] }
private def b3SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5723, 5724],
    outs := [5725] }
private def b3SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5725], outs := [5726],
    params := [4096, 1024] }
private def b3SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5726], outs := [5727] }
private def b3SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8582, 5727], outs := [5728] }

private def b3PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10092], outs := [10094],
    params := [2048, 1024] }
private def b3PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10093], outs := [10095],
    params := [2048, 1024] }
private def b3PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10094], outs := [10100],
    params := [2048, 1024] }
private def b3PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10095], outs := [10101],
    params := [2048, 1024] }
private def b3PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10100, 5724],
    outs := [10104] }
private def b3PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10101, 5724],
    outs := [10105] }
private def b3PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10104], outs := [10114],
    params := [2048, 1024] }
private def b3PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10105], outs := [10115],
    params := [2048, 1024] }
private def b3PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10114], outs := [10118] }
private def b3PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10115], outs := [10119] }
private def b3PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16154, 10118], outs := [10122] }
private def b3PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16162, 10119], outs := [10123] }

private theorem b3_red_sm5776 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5722 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5720) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 576 b3SmReshape0
    5720 5722 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5720 5722 [4096, 1024]

private theorem b3_red_pm10248 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10094 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10092) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1267 b3PmReshape0
    10092 10094 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3PmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10092 10094 [2048, 1024]

private theorem b3_red_pm10249 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10095 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10093) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1268 b3PmReshape1
    10093 10095 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3PmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10093 10095 [2048, 1024]

private theorem b3_red_sm5777 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5723 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5722) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 577 b3SmReshape1
    5722 5723 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5722 5723 [4096, 1024]

private theorem b3_red_pm10254 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10100 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10094) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1269 b3PmReshape10
    10094 10100 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10094 10100 [2048, 1024]

private theorem b3_red_pm10255 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10101 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10095) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1270 b3PmReshape11
    10095 10101 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10095 10101 [2048, 1024]

private theorem b3_red_sm5779 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5725 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5723)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5724) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 578 b3SmLinear
    5723 5724 5725 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold b3SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5723 5724 5725

private theorem b3_red_pm10258 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10104 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10100)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5724) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1271 b3PmLinear0
    10100 5724 10104 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold b3PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10100 5724 10104

private theorem b3_red_pm10259 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10105 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10101)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5724) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1272 b3PmLinear1
    10101 5724 10105 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold b3PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10101 5724 10105

private theorem b3_red_sm5780 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5726 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5725) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 579 b3SmView
    5725 5726 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5725 5726

private theorem b3_red_pm10268 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10114 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10104) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1273 b3PmView0
    10104 10114 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10104 10114

private theorem b3_red_pm10269 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10115 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10105) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1274 b3PmView1
    10105 10115 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10105 10115

private theorem b3_red_sm5781 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5727 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5726 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 580 b3SmFloat
    5726 5727 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5726 5727 []

private theorem b3_red_pm10272 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10118 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10114 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1275 b3PmFloat0
    10114 10118 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10114 10118 []

private theorem b3_red_pm10273 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10119 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10115 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1276 b3PmFloat1
    10115 10119 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10115 10119 []

private theorem b3_red_sm5782 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5728 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8582)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5727) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 581 b3SmAdd
    8582 5727 5728 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold b3SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8582 5727 5728

private theorem b3_red_pm10276 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10122 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16154)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10118) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1277 b3PmAdd0
    16154 10118 10122 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold b3PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16154 10118 10122

private theorem b3_red_pm10277 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10123 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16162)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10119) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1278 b3PmAdd1
    16162 10119 10123 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold b3PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16162 10119 10123

/-- The real canonical L12 block 3 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem goal1_l12_block3_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5720)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10092)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10093)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5724 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5724)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5724).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5727)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10118)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10119)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10094)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10095)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [b3_red_sm5776 initSM, b3_red_pm10248 initPM, b3_red_pm10249 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5723)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10101)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [b3_red_sm5777 initSM, b3_red_pm10254 initPM, b3_red_pm10255 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5725)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10104)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10105)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [b3_red_sm5779 initSM, b3_red_pm10258 initPM, b3_red_pm10259 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5726)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10114)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10115)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [b3_red_sm5780 initSM, b3_red_pm10268 initPM, b3_red_pm10269 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [b3_red_sm5781 initSM, b3_red_pm10272 initPM, b3_red_pm10273 initPM]
  exact hView

/-- Canonical L12 block 3 output relation at the exact values consumed by L21.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `5728 ↔ 10122/10123` relation is a conclusion, never a
caller contract. -/
theorem goal1_l12_block3_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8582)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16154)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16162)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5720)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10092)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10093)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5724 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5724)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5724).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5728)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := goal1_l12_block3_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [b3_red_sm5782 initSM, b3_red_pm10276 initPM, b3_red_pm10277 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms goal1_l12_block3_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
