/- Canonical Goal 1, layer 13: faithful attention projection and residual output. -/
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

private def cL13SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5774], outs := [5776],
    params := [4096, 1024] }
private def cL13SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5776], outs := [5777],
    params := [4096, 1024] }
private def cL13SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5777, 5778],
    outs := [5779] }
private def cL13SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5779], outs := [5780],
    params := [4096, 1024] }
private def cL13SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5780], outs := [5781] }
private def cL13SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8621, 5781], outs := [5782] }

private def cL13PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10246], outs := [10248],
    params := [2048, 1024] }
private def cL13PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10247], outs := [10249],
    params := [2048, 1024] }
private def cL13PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10248], outs := [10254],
    params := [2048, 1024] }
private def cL13PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10249], outs := [10255],
    params := [2048, 1024] }
private def cL13PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10254, 5778],
    outs := [10258] }
private def cL13PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10255, 5778],
    outs := [10259] }
private def cL13PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10258], outs := [10268],
    params := [2048, 1024] }
private def cL13PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10259], outs := [10269],
    params := [2048, 1024] }
private def cL13PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10268], outs := [10272] }
private def cL13PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10269], outs := [10273] }
private def cL13PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16186, 10272], outs := [10276] }
private def cL13PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16194, 10273], outs := [10277] }

private theorem cL13_red_sm5776 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5776 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5774) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 611 cL13SmReshape0
    5774 5776 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5774 5776 [4096, 1024]

private theorem cL13_red_pm10248 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10248 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10246) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1343 cL13PmReshape0
    10246 10248 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13PmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10246 10248 [2048, 1024]

private theorem cL13_red_pm10249 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10249 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10247) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1344 cL13PmReshape1
    10247 10249 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13PmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10247 10249 [2048, 1024]

private theorem cL13_red_sm5777 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5777 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5776) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 612 cL13SmReshape1
    5776 5777 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5776 5777 [4096, 1024]

private theorem cL13_red_pm10254 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10254 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10248) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1345 cL13PmReshape10
    10248 10254 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10248 10254 [2048, 1024]

private theorem cL13_red_pm10255 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10255 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10249) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1346 cL13PmReshape11
    10249 10255 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10249 10255 [2048, 1024]

private theorem cL13_red_sm5779 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5779 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5777)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5778) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 613 cL13SmLinear
    5777 5778 5779 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL13SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5777 5778 5779

private theorem cL13_red_pm10258 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10258 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10254)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5778) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1347 cL13PmLinear0
    10254 5778 10258 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL13PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10254 5778 10258

private theorem cL13_red_pm10259 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10259 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10255)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5778) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1348 cL13PmLinear1
    10255 5778 10259 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL13PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10255 5778 10259

private theorem cL13_red_sm5780 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5780 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5779) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 614 cL13SmView
    5779 5780 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5779 5780

private theorem cL13_red_pm10268 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10268 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10258) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1349 cL13PmView0
    10258 10268 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10258 10268

private theorem cL13_red_pm10269 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10269 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10259) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1350 cL13PmView1
    10259 10269 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10259 10269

private theorem cL13_red_sm5781 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5781 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5780 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 615 cL13SmFloat
    5780 5781 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5780 5781 []

private theorem cL13_red_pm10272 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10272 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10268 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1351 cL13PmFloat0
    10268 10272 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10268 10272 []

private theorem cL13_red_pm10273 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10273 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10269 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1352 cL13PmFloat1
    10269 10273 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL13PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10269 10273 []

private theorem cL13_red_sm5782 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5782 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8621)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5781) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 616 cL13SmAdd
    8621 5781 5782 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL13SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8621 5781 5782

private theorem cL13_red_pm10276 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10276 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16186)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10272) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1353 cL13PmAdd0
    16186 10272 10276 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL13PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16186 10272 10276

private theorem cL13_red_pm10277 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10277 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16194)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10273) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1354 cL13PmAdd1
    16194 10273 10277 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL13PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16194 10273 10277

/-- The real canonical L13 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l13_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5774)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10246)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10247)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5778 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5778)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5778).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5781)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10272)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10273)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5776)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10248)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10249)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL13_red_sm5776 initSM, cL13_red_pm10248 initPM, cL13_red_pm10249 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5777)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10254)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10255)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL13_red_sm5777 initSM, cL13_red_pm10254 initPM, cL13_red_pm10255 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5779)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10258)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10259)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL13_red_sm5779 initSM, cL13_red_pm10258 initPM, cL13_red_pm10259 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5780)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10268)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10269)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL13_red_sm5780 initSM, cL13_red_pm10268 initPM, cL13_red_pm10269 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL13_red_sm5781 initSM, cL13_red_pm10272 initPM, cL13_red_pm10273 initPM]
  exact hView

/-- Canonical L13 output relation at the exact values consumed by L21.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `5782 ↔ 10276/10277` relation is a conclusion, never a
caller contract. -/
theorem canonical_l13_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8621)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16186)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16194)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5774)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10246)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10247)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5778 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5778)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5778).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10277)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l13_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL13_red_sm5782 initSM, cL13_red_pm10276 initPM, cL13_red_pm10277 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l13_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
