/- Canonical Goal 1, layer 12: faithful attention projection and residual output. -/
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

private def cL12SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5612], outs := [5614],
    params := [4096, 1024] }
private def cL12SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5614], outs := [5615],
    params := [4096, 1024] }
private def cL12SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5615, 5616],
    outs := [5617] }
private def cL12SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5617], outs := [5618],
    params := [4096, 1024] }
private def cL12SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5618], outs := [5619] }
private def cL12SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8504, 5619], outs := [5620] }

private def cL12PmReshape00 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9782], outs := [9784],
    params := [2048, 1024] }
private def cL12PmReshape01 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9783], outs := [9785],
    params := [2048, 1024] }
private def cL12PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9784], outs := [9790],
    params := [2048, 1024] }
private def cL12PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9785], outs := [9791],
    params := [2048, 1024] }
private def cL12PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9790, 5616],
    outs := [9794] }
private def cL12PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9791, 5616],
    outs := [9795] }
private def cL12PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9794], outs := [9804],
    params := [2048, 1024] }
private def cL12PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9795], outs := [9805],
    params := [2048, 1024] }
private def cL12PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9804], outs := [9808] }
private def cL12PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9805], outs := [9809] }
private def cL12PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16090, 9808], outs := [9812] }
private def cL12PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16098, 9809], outs := [9813] }

private theorem cL12_red_sm6154 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5614 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5612) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 506 cL12SmReshape0
    5612 5614 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5612 5614 [4096, 1024]

private theorem cL12_red_pm11326 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9784 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9782) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1115 cL12PmReshape00
    9782 9784 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12PmReshape00
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9782 9784 [2048, 1024]

private theorem cL12_red_pm11327 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9785 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9783) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1116 cL12PmReshape01
    9783 9785 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12PmReshape01
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9783 9785 [2048, 1024]

private theorem cL12_red_sm6155 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5615 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5614) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 507 cL12SmReshape1
    5614 5615 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5614 5615 [4096, 1024]

private theorem cL12_red_pm11332 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9790 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9784) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1117 cL12PmReshape10
    9784 9790 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9784 9790 [2048, 1024]

private theorem cL12_red_pm11333 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9791 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9785) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1118 cL12PmReshape11
    9785 9791 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9785 9791 [2048, 1024]

private theorem cL12_red_sm6157 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5617 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5615)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5616) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 508 cL12SmLinear
    5615 5616 5617 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5615 5616 5617

private theorem cL12_red_pm11336 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9794 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9790)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5616) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1119 cL12PmLinear0
    9790 5616 9794 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9790 5616 9794

private theorem cL12_red_pm11337 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9795 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9791)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5616) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1120 cL12PmLinear1
    9791 5616 9795 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9791 5616 9795

private theorem cL12_red_sm6158 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5618 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5617) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 509 cL12SmView
    5617 5618 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5617 5618

private theorem cL12_red_pm11346 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9804 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9794) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1121 cL12PmView0
    9794 9804 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9794 9804

private theorem cL12_red_pm11347 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9805 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 9795) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1122 cL12PmView1
    9795 9805 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9795 9805

private theorem cL12_red_sm6159 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5619 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5618 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 510 cL12SmFloat
    5618 5619 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5618 5619 []

private theorem cL12_red_pm11350 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9808 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9804 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1123 cL12PmFloat0
    9804 9808 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 9804 9808 []

private theorem cL12_red_pm11351 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9809 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9805 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1124 cL12PmFloat1
    9805 9809 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 9805 9809 []

private theorem cL12_red_sm6160 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5620 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8504)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5619) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 511 cL12SmAdd
    8504 5619 5620 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8504 5619 5620

private theorem cL12_red_pm11354 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9812 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16090)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9808) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1125 cL12PmAdd0
    16090 9808 9812 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16090 9808 9812

private theorem cL12_red_pm11355 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9813 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16098)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9809) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1126 cL12PmAdd1
    16098 9809 9813 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16098 9809 9813

/-- The real canonical L12 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l12_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5612)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9783)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5616 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5616)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5616).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5619)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9808)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9809)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5614)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9784)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9785)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL12_red_sm6154 initSM, cL12_red_pm11326 initPM, cL12_red_pm11327 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5615)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9790)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9791)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL12_red_sm6155 initSM, cL12_red_pm11332 initPM, cL12_red_pm11333 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5617)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9794)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9795)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL12_red_sm6157 initSM, cL12_red_pm11336 initPM, cL12_red_pm11337 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5618)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9804)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9805)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL12_red_sm6158 initSM, cL12_red_pm11346 initPM, cL12_red_pm11347 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL12_red_sm6159 initSM, cL12_red_pm11350 initPM, cL12_red_pm11351 initPM]
  exact hView

/-- Canonical L12 output relation at the exact values consumed by L21.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `5620 ↔ 9812/9813` relation is a conclusion, never a
caller contract. -/
theorem canonical_l12_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8504)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16090)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16098)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5612)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9783)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5616 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5616)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5616).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l12_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL12_red_sm6160 initSM, cL12_red_pm11354 initPM, cL12_red_pm11355 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l12_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
