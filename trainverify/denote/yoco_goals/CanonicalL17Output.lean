/- Canonical Goal 1, layer 17: faithful attention projection and residual output. -/
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

private def cL17SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5990], outs := [5992],
    params := [4096, 1024] }
private def cL17SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5992], outs := [5993],
    params := [4096, 1024] }
private def cL17SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5993, 5994],
    outs := [5995] }
private def cL17SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5995], outs := [5996],
    params := [4096, 1024] }
private def cL17SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5996], outs := [5997] }
private def cL17SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8777, 5997], outs := [5998] }

private def cL17PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10862], outs := [10864],
    params := [2048, 1024] }
private def cL17PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10863], outs := [10865],
    params := [2048, 1024] }
private def cL17PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10864], outs := [10870],
    params := [2048, 1024] }
private def cL17PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10865], outs := [10871],
    params := [2048, 1024] }
private def cL17PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10870, 5994],
    outs := [10874] }
private def cL17PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10871, 5994],
    outs := [10875] }
private def cL17PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10874], outs := [10884],
    params := [2048, 1024] }
private def cL17PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10875], outs := [10885],
    params := [2048, 1024] }
private def cL17PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10884], outs := [10888] }
private def cL17PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10885], outs := [10889] }
private def cL17PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16314, 10888], outs := [10892] }
private def cL17PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16322, 10889], outs := [10893] }

private theorem cL17_red_sm5776 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5992 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5990) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 751 cL17SmReshape0
    5990 5992 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5990 5992 [4096, 1024]

private theorem cL17_red_pm10248 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10864 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10862) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1647 cL17PmReshape0
    10862 10864 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17PmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10862 10864 [2048, 1024]

private theorem cL17_red_pm10249 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10865 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10863) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1648 cL17PmReshape1
    10863 10865 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17PmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10863 10865 [2048, 1024]

private theorem cL17_red_sm5777 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5993 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5992) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 752 cL17SmReshape1
    5992 5993 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5992 5993 [4096, 1024]

private theorem cL17_red_pm10254 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10870 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10864) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1649 cL17PmReshape10
    10864 10870 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10864 10870 [2048, 1024]

private theorem cL17_red_pm10255 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10871 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10865) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1650 cL17PmReshape11
    10865 10871 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10865 10871 [2048, 1024]

private theorem cL17_red_sm5779 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5995 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5993)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5994) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 753 cL17SmLinear
    5993 5994 5995 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL17SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5993 5994 5995

private theorem cL17_red_pm10258 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10874 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10870)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5994) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1651 cL17PmLinear0
    10870 5994 10874 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL17PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10870 5994 10874

private theorem cL17_red_pm10259 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10875 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10871)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5994) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1652 cL17PmLinear1
    10871 5994 10875 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL17PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10871 5994 10875

private theorem cL17_red_sm5780 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5996 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5995) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 754 cL17SmView
    5995 5996 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5995 5996

private theorem cL17_red_pm10268 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10884 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10874) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1653 cL17PmView0
    10874 10884 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10874 10884

private theorem cL17_red_pm10269 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10885 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10875) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1654 cL17PmView1
    10875 10885 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10875 10885

private theorem cL17_red_sm5781 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5997 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5996 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 755 cL17SmFloat
    5996 5997 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5996 5997 []

private theorem cL17_red_pm10272 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10888 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10884 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1655 cL17PmFloat0
    10884 10888 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10884 10888 []

private theorem cL17_red_pm10273 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10889 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10885 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1656 cL17PmFloat1
    10885 10889 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10885 10889 []

private theorem cL17_red_sm5782 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5998 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8777)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5997) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 756 cL17SmAdd
    8777 5997 5998 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL17SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8777 5997 5998

private theorem cL17_red_pm10276 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10892 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16314)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10888) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1657 cL17PmAdd0
    16314 10888 10892 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL17PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16314 10888 10892

private theorem cL17_red_pm10277 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10893 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16322)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10889) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1658 cL17PmAdd1
    16322 10889 10893 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL17PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16322 10889 10893

/-- The real canonical L17 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l17_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10862)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10863)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5994 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5994)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5994).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5997)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10888)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10889)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5992)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10864)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10865)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL17_red_sm5776 initSM, cL17_red_pm10248 initPM, cL17_red_pm10249 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5993)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10870)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10871)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL17_red_sm5777 initSM, cL17_red_pm10254 initPM, cL17_red_pm10255 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5995)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10874)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10875)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL17_red_sm5779 initSM, cL17_red_pm10258 initPM, cL17_red_pm10259 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5996)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10885)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL17_red_sm5780 initSM, cL17_red_pm10268 initPM, cL17_red_pm10269 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL17_red_sm5781 initSM, cL17_red_pm10272 initPM, cL17_red_pm10273 initPM]
  exact hView

/-- Canonical L17 output relation at the exact values consumed by the L17 MoE tail.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `5998 ↔ 10892/10893` relation is a conclusion, never a
caller contract. -/
theorem canonical_l17_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8777)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16314)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16322)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10862)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10863)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5994 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5994)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5994).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10893)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l17_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL17_red_sm5782 initSM, cL17_red_pm10276 initPM, cL17_red_pm10277 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l17_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
