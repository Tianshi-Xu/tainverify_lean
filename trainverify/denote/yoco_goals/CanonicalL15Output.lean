/- Canonical Goal 1, layer 14: faithful attention projection and residual output. -/
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

private def cL15SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5882], outs := [5884],
    params := [4096, 1024] }
private def cL15SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5884], outs := [5885],
    params := [4096, 1024] }
private def cL15SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5885, 5886],
    outs := [5887] }
private def cL15SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5887], outs := [5888],
    params := [4096, 1024] }
private def cL15SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5888], outs := [5889] }
private def cL15SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8699, 5889], outs := [5890] }

private def cL15PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10554], outs := [10556],
    params := [2048, 1024] }
private def cL15PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10555], outs := [10557],
    params := [2048, 1024] }
private def cL15PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10556], outs := [10562],
    params := [2048, 1024] }
private def cL15PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10557], outs := [10563],
    params := [2048, 1024] }
private def cL15PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10562, 5886],
    outs := [10566] }
private def cL15PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10563, 5886],
    outs := [10567] }
private def cL15PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10566], outs := [10576],
    params := [2048, 1024] }
private def cL15PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10567], outs := [10577],
    params := [2048, 1024] }
private def cL15PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10576], outs := [10580] }
private def cL15PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10577], outs := [10581] }
private def cL15PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16250, 10580], outs := [10584] }
private def cL15PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16258, 10581], outs := [10585] }

private theorem cL15_red_sm5776 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5884 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5882) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 681 cL15SmReshape0
    5882 5884 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5882 5884 [4096, 1024]

private theorem cL15_red_pm10248 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10556 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10554) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1495 cL15PmReshape0
    10554 10556 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15PmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10554 10556 [2048, 1024]

private theorem cL15_red_pm10249 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10557 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10555) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1496 cL15PmReshape1
    10555 10557 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15PmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10555 10557 [2048, 1024]

private theorem cL15_red_sm5777 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5885 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5884) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 682 cL15SmReshape1
    5884 5885 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5884 5885 [4096, 1024]

private theorem cL15_red_pm10254 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10562 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10556) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1497 cL15PmReshape10
    10556 10562 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10556 10562 [2048, 1024]

private theorem cL15_red_pm10255 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10563 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10557) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1498 cL15PmReshape11
    10557 10563 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10557 10563 [2048, 1024]

private theorem cL15_red_sm5779 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5887 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5885)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5886) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 683 cL15SmLinear
    5885 5886 5887 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL15SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5885 5886 5887

private theorem cL15_red_pm10258 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10566 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10562)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5886) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1499 cL15PmLinear0
    10562 5886 10566 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL15PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10562 5886 10566

private theorem cL15_red_pm10259 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10567 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10563)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5886) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1500 cL15PmLinear1
    10563 5886 10567 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL15PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10563 5886 10567

private theorem cL15_red_sm5780 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5888 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5887) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 684 cL15SmView
    5887 5888 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5887 5888

private theorem cL15_red_pm10268 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10576 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10566) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1501 cL15PmView0
    10566 10576 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10566 10576

private theorem cL15_red_pm10269 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10577 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10567) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1502 cL15PmView1
    10567 10577 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10567 10577

private theorem cL15_red_sm5781 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5889 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5888 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 685 cL15SmFloat
    5888 5889 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5888 5889 []

private theorem cL15_red_pm10272 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10580 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10576 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1503 cL15PmFloat0
    10576 10580 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10576 10580 []

private theorem cL15_red_pm10273 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10581 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10577 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1504 cL15PmFloat1
    10577 10581 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10577 10581 []

private theorem cL15_red_sm5782 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5890 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8699)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5889) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 686 cL15SmAdd
    8699 5889 5890 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL15SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8699 5889 5890

private theorem cL15_red_pm10276 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10584 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16250)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10580) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1505 cL15PmAdd0
    16250 10580 10584 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL15PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16250 10580 10584

private theorem cL15_red_pm10277 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10585 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16258)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10581) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1506 cL15PmAdd1
    16258 10581 10585 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL15PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16258 10581 10585

/-- The real canonical L15 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l15_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5882)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10554)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10555)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5886 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5886)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5886).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5889)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10580)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10581)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10556)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10557)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL15_red_sm5776 initSM, cL15_red_pm10248 initPM, cL15_red_pm10249 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5885)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10563)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL15_red_sm5777 initSM, cL15_red_pm10254 initPM, cL15_red_pm10255 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5887)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10566)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10567)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL15_red_sm5779 initSM, cL15_red_pm10258 initPM, cL15_red_pm10259 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5888)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10576)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10577)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL15_red_sm5780 initSM, cL15_red_pm10268 initPM, cL15_red_pm10269 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL15_red_sm5781 initSM, cL15_red_pm10272 initPM, cL15_red_pm10273 initPM]
  exact hView

/-- Canonical L15 output relation at the exact values consumed by L21.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `5890 ↔ 10584/10585` relation is a conclusion, never a
caller contract. -/
theorem canonical_l15_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8699)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16250)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16258)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5882)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10554)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10555)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5886 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5886)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5886).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10584)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l15_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL15_red_sm5782 initSM, cL15_red_pm10276 initPM, cL15_red_pm10277 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l15_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
