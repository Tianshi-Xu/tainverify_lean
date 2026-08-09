/- Canonical Goal 1, layer 12 block 2: faithful attention projection and residual output. -/
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

private def cL12B2SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5666], outs := [5668],
    params := [4096, 1024] }
private def cL12B2SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5668], outs := [5669],
    params := [4096, 1024] }
private def cL12B2SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5669, 5670],
    outs := [5671] }
private def cL12B2SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5671], outs := [5672],
    params := [4096, 1024] }
private def cL12B2SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5672], outs := [5673] }
private def cL12B2SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8543, 5673], outs := [5674] }

private def cL12B2PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9938], outs := [9940],
    params := [2048, 1024] }
private def cL12B2PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9939], outs := [9941],
    params := [2048, 1024] }
private def cL12B2PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9940], outs := [9946],
    params := [2048, 1024] }
private def cL12B2PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9941], outs := [9947],
    params := [2048, 1024] }
private def cL12B2PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9946, 5670],
    outs := [9950] }
private def cL12B2PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9947, 5670],
    outs := [9951] }
private def cL12B2PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9950], outs := [9960],
    params := [2048, 1024] }
private def cL12B2PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9951], outs := [9961],
    params := [2048, 1024] }
private def cL12B2PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9960], outs := [9964] }
private def cL12B2PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9961], outs := [9965] }
private def cL12B2PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16122, 9964], outs := [9968] }
private def cL12B2PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16130, 9965], outs := [9969] }

private theorem cL12B2_red_sm5668 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5668 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5666) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 541 cL12B2SmReshape0
    5666 5668 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5666 5668 [4096, 1024]

private theorem cL12B2_red_pm9940 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9940 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9938) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1191 cL12B2PmReshape0
    9938 9940 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9938 9940 [2048, 1024]

private theorem cL12B2_red_pm9941 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9941 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9939) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1192 cL12B2PmReshape1
    9939 9941 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9939 9941 [2048, 1024]

private theorem cL12B2_red_sm5669 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5669 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5668) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 542 cL12B2SmReshape1
    5668 5669 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5668 5669 [4096, 1024]

private theorem cL12B2_red_pm9946 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9946 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9940) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1193 cL12B2PmReshape10
    9940 9946 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9940 9946 [2048, 1024]

private theorem cL12B2_red_pm9947 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9947 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9941) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1194 cL12B2PmReshape11
    9941 9947 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9941 9947 [2048, 1024]

private theorem cL12B2_red_sm5671 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5671 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5669)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5670) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 543 cL12B2SmLinear
    5669 5670 5671 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12B2SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5669 5670 5671

private theorem cL12B2_red_pm9950 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9950 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9946)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5670) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1195 cL12B2PmLinear0
    9946 5670 9950 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9946 5670 9950

private theorem cL12B2_red_pm9951 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9951 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9947)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5670) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1196 cL12B2PmLinear1
    9947 5670 9951 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9947 5670 9951

private theorem cL12B2_red_sm5672 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5672 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5671) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 544 cL12B2SmView
    5671 5672 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5671 5672

private theorem cL12B2_red_pm9960 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9960 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9950) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1197 cL12B2PmView0
    9950 9960 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9950 9960

private theorem cL12B2_red_pm9961 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9961 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9951) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1198 cL12B2PmView1
    9951 9961 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9951 9961

private theorem cL12B2_red_sm5673 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5673 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5672 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 545 cL12B2SmFloat
    5672 5673 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5672 5673 []

private theorem cL12B2_red_pm9964 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9964 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9960 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1199 cL12B2PmFloat0
    9960 9964 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9960 9964 []

private theorem cL12B2_red_pm9965 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9965 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9961 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1200 cL12B2PmFloat1
    9961 9965 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9961 9965 []

private theorem cL12B2_red_sm5674 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5674 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8543)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5673) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 546 cL12B2SmAdd
    8543 5673 5674 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12B2SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8543 5673 5674

private theorem cL12B2_red_pm9968 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9968 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16122)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9964) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1201 cL12B2PmAdd0
    16122 9964 9968 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16122 9964 9968

private theorem cL12B2_red_pm9969 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9969 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16130)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9965) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1202 cL12B2PmAdd1
    16130 9965 9969 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12B2PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16130 9965 9969

/-- The real canonical L12 block 2 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l12b2_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9938)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9939)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5670 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5670)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5670).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5673)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9964)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9965)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5668)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9940)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9941)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL12B2_red_sm5668 initSM, cL12B2_red_pm9940 initPM, cL12B2_red_pm9941 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5669)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9947)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL12B2_red_sm5669 initSM, cL12B2_red_pm9946 initPM, cL12B2_red_pm9947 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5671)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9950)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9951)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL12B2_red_sm5671 initSM, cL12B2_red_pm9950 initPM, cL12B2_red_pm9951 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5672)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9960)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9961)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL12B2_red_sm5672 initSM, cL12B2_red_pm9960 initPM, cL12B2_red_pm9961 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL12B2_red_sm5673 initSM, cL12B2_red_pm9964 initPM, cL12B2_red_pm9965 initPM]
  exact hView

/-- Canonical L12 block 2 output relation at the exact values consumed by L21.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `5674 ↔ 9968/9969` relation is a conclusion, never a
caller contract. -/
theorem canonical_l12b2_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8543)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16130)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9938)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9939)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5670 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5670)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5670).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l12b2_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL12B2_red_sm5674 initSM, cL12B2_red_pm9968 initPM, cL12B2_red_pm9969 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l12b2_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns

