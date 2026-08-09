/- Canonical Goal 1, layer 15: faithful attention projection and residual output. -/
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

private def cL16SmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5936], outs := [5938],
    params := [4096, 1024] }
private def cL16SmReshape1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5938], outs := [5939],
    params := [4096, 1024] }
private def cL16SmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5939, 5940],
    outs := [5941] }
private def cL16SmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5941], outs := [5942],
    params := [4096, 1024] }
private def cL16SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5942], outs := [5943] }
private def cL16SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8738, 5943], outs := [5944] }

private def cL16PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10708], outs := [10710],
    params := [2048, 1024] }
private def cL16PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10709], outs := [10711],
    params := [2048, 1024] }
private def cL16PmReshape10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10710], outs := [10716],
    params := [2048, 1024] }
private def cL16PmReshape11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10711], outs := [10717],
    params := [2048, 1024] }
private def cL16PmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10716, 5940],
    outs := [10720] }
private def cL16PmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10717, 5940],
    outs := [10721] }
private def cL16PmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10720], outs := [10730],
    params := [2048, 1024] }
private def cL16PmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10721], outs := [10731],
    params := [2048, 1024] }
private def cL16PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10730], outs := [10734] }
private def cL16PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10731], outs := [10735] }
private def cL16PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16282, 10734], outs := [10738] }
private def cL16PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16290, 10735], outs := [10739] }

private theorem cL16_red_sm5776 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5938 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5936) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 716 cL16SmReshape0
    5936 5938 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16SmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5936 5938 [4096, 1024]

private theorem cL16_red_pm10248 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10710 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10708) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1571 cL16PmReshape0
    10708 10710 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16PmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10708 10710 [2048, 1024]

private theorem cL16_red_pm10249 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10711 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10709) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1572 cL16PmReshape1
    10709 10711 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16PmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10709 10711 [2048, 1024]

private theorem cL16_red_sm5777 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5939 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5938) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 717 cL16SmReshape1
    5938 5939 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16SmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5938 5939 [4096, 1024]

private theorem cL16_red_pm10254 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10716 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10710) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1573 cL16PmReshape10
    10710 10716 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16PmReshape10
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10710 10716 [2048, 1024]

private theorem cL16_red_pm10255 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10717 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10711) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1574 cL16PmReshape11
    10711 10717 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16PmReshape11
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10711 10717 [2048, 1024]

private theorem cL16_red_sm5779 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5941 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5939)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5940) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 718 cL16SmLinear
    5939 5940 5941 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL16SmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5939 5940 5941

private theorem cL16_red_pm10258 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10720 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10716)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5940) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1575 cL16PmLinear0
    10716 5940 10720 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL16PmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10716 5940 10720

private theorem cL16_red_pm10259 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10721 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10717)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5940) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1576 cL16PmLinear1
    10717 5940 10721 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL16PmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10717 5940 10721

private theorem cL16_red_sm5780 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5942 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 5941) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 719 cL16SmView
    5941 5942 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16SmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5941 5942

private theorem cL16_red_pm10268 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10730 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10720) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1577 cL16PmView0
    10720 10730 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16PmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10720 10730

private theorem cL16_red_pm10269 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10731 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 10721) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1578 cL16PmView1
    10721 10731 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16PmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10721 10731

private theorem cL16_red_sm5781 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5943 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5942 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 720 cL16SmFloat
    5942 5943 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 5942 5943 []

private theorem cL16_red_pm10272 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10734 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10730 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1579 cL16PmFloat0
    10730 10734 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 10730 10734 []

private theorem cL16_red_pm10273 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10735 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10731 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1580 cL16PmFloat1
    10731 10735 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 10731 10735 []

private theorem cL16_red_sm5782 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5944 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8738)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5943) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 721 cL16SmAdd
    8738 5943 5944 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL16SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8738 5943 5944

private theorem cL16_red_pm10276 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10738 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16282)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10734) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1581 cL16PmAdd0
    16282 10734 10738 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL16PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16282 10734 10738

private theorem cL16_red_pm10277 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10739 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16290)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10735) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1582 cL16PmAdd1
    16290 10735 10739 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL16PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16290 10735 10739

/-- The real canonical L16 attention-output projection (two reshapes, linear,
view, and float) preserves the CP2 zigzag layout.  The weight premises are
ordinary independently-checkable input facts, not a relation over a computed
intermediate. -/
theorem canonical_l16_projection_from_attention (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5936)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10708)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10709)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5940 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5940)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5940).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5943)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10734)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10735)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hReshape0 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5938)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10710)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10711)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL16_red_sm5776 initSM, cL16_red_pm10248 initPM, cL16_red_pm10249 initPM]
    exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hAttention
      (by decide) (by decide) (by decide)
  have hReshape1 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5939)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10716)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10717)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL16_red_sm5777 initSM, cL16_red_pm10254 initPM, cL16_red_pm10255 initPM]
    exact Zigzag2Rel.view_id' hReshape0
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5941)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10720)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10721)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL16_red_sm5779 initSM, cL16_red_pm10258 initPM, cL16_red_pm10259 initPM,
      hWeight]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hReshape1 hWeightShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5942)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10730)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10731)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL16_red_sm5780 initSM, cL16_red_pm10268 initPM, cL16_red_pm10269 initPM]
    exact Zigzag2Rel.view_id' hLinear
  rw [cL16_red_sm5781 initSM, cL16_red_pm10272 initPM, cL16_red_pm10273 initPM]
  exact hView

/-- Canonical L16 output relation at the exact values consumed by L21.
All six concrete tail operators on each side are reduced from the real Goal-1
graph; the computed `5944 ↔ 10738/10739` relation is a conclusion, never a
caller contract. -/
theorem canonical_l16_output_from_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16282)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16290)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5936)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10708)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10709)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hWeight : denoteGraphDistributedFaithful sm_goal_1 initSM 5940 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5940)
    (hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5940).shape = [1024, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hProjection := canonical_l16_projection_from_attention initSM initPM
    hAttention hWeight hWeightShape
  rw [cL16_red_sm5782 initSM, cL16_red_pm10276 initPM, cL16_red_pm10277 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hProjection (by decide) (by decide)

#print axioms canonical_l16_output_from_inputs

end
end TrainVerify.Denote.GeneratedPatterns
