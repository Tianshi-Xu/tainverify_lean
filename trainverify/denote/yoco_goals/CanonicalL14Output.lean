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

private def cL14SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5828], outs := [5830],
    params := [4096, 1024] }
private def cL14SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5830], outs := [5831],
    params := [4096, 1024] }
private def cL14SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5831, 5832],
    outs := [5833] }
private def cL14SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5833], outs := [5834],
    params := [4096, 1024] }
private def cL14SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5834], outs := [5835] }
private def cL14SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8660, 5835], outs := [5836] }

private def cL14PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10400], outs := [10402],
    params := [2048, 1024] }
private def cL14PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10401], outs := [10403],
    params := [2048, 1024] }
private def cL14PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10402], outs := [10408],
    params := [2048, 1024] }
private def cL14PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10403], outs := [10409],
    params := [2048, 1024] }
private def cL14PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10408, 5832],
    outs := [10412] }
private def cL14PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10409, 5832],
    outs := [10413] }
private def cL14PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10412], outs := [10422],
    params := [2048, 1024] }
private def cL14PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10413], outs := [10423],
    params := [2048, 1024] }
private def cL14PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10422], outs := [10426] }
private def cL14PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10423], outs := [10427] }
private def cL14PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16218, 10426], outs := [10430] }
private def cL14PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16226, 10427], outs := [10431] }

private theorem cL14_red_sm5776 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5830 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5828) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 646 cL14SmReshape0
    5828 5830 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5828 5830 [4096, 1024]

private theorem cL14_red_pm10248 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10402 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10400) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1419 cL14PmReshape0
    10400 10402 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14PmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10400 10402 [2048, 1024]

private theorem cL14_red_pm10249 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10403 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10401) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1420 cL14PmReshape1
    10401 10403 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14PmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10401 10403 [2048, 1024]

private theorem cL14_red_sm5777 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5831 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5830) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 647 cL14SmReshape1
    5830 5831 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5830 5831 [4096, 1024]

private theorem cL14_red_pm10254 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10408 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10402) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1421 cL14PmReshape10
    10402 10408 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10402 10408 [2048, 1024]

private theorem cL14_red_pm10255 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10409 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10403) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1422 cL14PmReshape11
    10403 10409 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10403 10409 [2048, 1024]

private theorem cL14_red_sm5779 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5833 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5831)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5832) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 648 cL14SmLinear
    5831 5832 5833 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL14SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5831 5832 5833

private theorem cL14_red_pm10258 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10412 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10408)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5832) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1423 cL14PmLinear0
    10408 5832 10412 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL14PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10408 5832 10412

private theorem cL14_red_pm10259 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10413 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10409)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5832) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1424 cL14PmLinear1
    10409 5832 10413 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL14PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10409 5832 10413

private theorem cL14_red_sm5780 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5834 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5833) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 649 cL14SmView
    5833 5834 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5833 5834

private theorem cL14_red_pm10268 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10422 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10412) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1425 cL14PmView0
    10412 10422 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10412 10422

private theorem cL14_red_pm10269 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10423 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10413) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1426 cL14PmView1
    10413 10423 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10413 10423

private theorem cL14_red_sm5781 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5835 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5834 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 650 cL14SmFloat
    5834 5835 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5834 5835 []

private theorem cL14_red_pm10272 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10426 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10422 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1427 cL14PmFloat0
    10422 10426 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10422 10426 []

private theorem cL14_red_pm10273 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10427 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10423 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1428 cL14PmFloat1
    10423 10427 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10423 10427 []

private theorem cL14_red_sm5782 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5836 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8660)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5835) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 651 cL14SmAdd
    8660 5835 5836 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL14SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8660 5835 5836

private theorem cL14_red_pm10276 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10430 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16218)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10426) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1429 cL14PmAdd0
    16218 10426 10430 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL14PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16218 10426 10430

private theorem cL14_red_pm10277 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10431 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16226)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10427) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1430 cL14PmAdd1
    16226 10427 10431 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL14PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16226 10427 10431

/-- The real canonical L14 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l14_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10400)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10401)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5832 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5832)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5832).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5835)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10426)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10427)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5830)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10402)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10403)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL14_red_sm5776 initSM, cL14_red_pm10248 initPM, cL14_red_pm10249 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5831)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10408)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10409)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL14_red_sm5777 initSM, cL14_red_pm10254 initPM, cL14_red_pm10255 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5833)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10412)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10413)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL14_red_sm5779 initSM, cL14_red_pm10258 initPM, cL14_red_pm10259 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5834)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10422)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10423)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL14_red_sm5780 initSM, cL14_red_pm10268 initPM, cL14_red_pm10269 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL14_red_sm5781 initSM, cL14_red_pm10272 initPM, cL14_red_pm10273 initPM]
  exact hView

/-- Canonical L14 output relation at the exact values consumed by L21.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `5836 ↔ 10430/10431` relation is a conclusion, never a
caller contract. -/
theorem canonical_l14_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8660)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16218)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16226)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10400)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10401)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5832 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5832)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5832).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10431)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l14_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL14_red_sm5782 initSM, cL14_red_pm10276 initPM, cL14_red_pm10277 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l14_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
