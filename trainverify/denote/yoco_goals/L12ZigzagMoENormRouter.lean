/- Canonical Goal 1, layer 12: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.L12ZigzagMoEResidualGate
import denote.yoco_goals.ZigzagPointwiseRel
import denote.MultirefGeneral

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

private def l12ZMnSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5620],
    outs := [8508, 8512], params := [2] }
private def l12ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9812],
    outs := [16102, 16106], params := [2] }
private def l12ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9813],
    outs := [16110, 16114], params := [2] }
private def l12ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8508, 5621], outs := [5622] }
private def l12ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16102, 5621], outs := [9818] }
private def l12ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16110, 5621], outs := [9819] }
private def l12ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5622],
    outs := [8519, 8523, 8527, 8531, 8535], params := [5] }
private def l12ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9818],
    outs := [15388, 13932, 13942, 13956, 13968], params := [5] }
private def l12ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9819],
    outs := [15390, 13933, 13943, 13957, 13969], params := [5] }

private theorem l12ZMn_red_sm8508 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8508 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5620 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 512 l12ZMnSmRef2
    5620 8508 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5620 [8508, 8512] 2 rfl 8508
    (by decide)

private theorem l12ZMn_red_pm16102 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16102 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9812 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1127 l12ZMnPmRef20
    9812 16102 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9812 [16102, 16106] 2 rfl 16102
    (by decide)

private theorem l12ZMn_red_pm16110 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16110 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9813 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1128 l12ZMnPmRef21
    9813 16110 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9813 [16110, 16114] 2 rfl 16110
    (by decide)

private theorem l12ZMn_red_sm5622 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5622 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8508)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5621) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 513 l12ZMnSmRms
    8508 5621 5622 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8508 5621 5622

private theorem l12ZMn_red_pm9818 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9818 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16102)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5621) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1129 l12ZMnPmRms0
    16102 5621 9818 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16102 5621 9818

private theorem l12ZMn_red_pm9819 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9819 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16110)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5621) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1130 l12ZMnPmRms1
    16110 5621 9819 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16110 5621 9819

private theorem l12ZMn_red_sm8523 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8523 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 514 l12ZMnSmRef5
    5622 8523 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622 [8519, 8523, 8527, 8531, 8535]
    5 rfl 8523 (by decide)

private theorem l12ZMn_red_pm13932 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13932 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1131 l12ZMnPmRef50
    9818 13932 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818
    [15388, 13932, 13942, 13956, 13968] 5 rfl 13932 (by decide)

private theorem l12ZMn_red_pm13933 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13933 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1132 l12ZMnPmRef51
    9819 13933 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819
    [15390, 13933, 13943, 13957, 13969] 5 rfl 13933 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 5621. -/
theorem l12_zigzag_moe_weight5621_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5621 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5621 := by
  have h := hInit initGoal_5621 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5621 pm_goal_1.numRanks _ rfl,
    show initGoal_5621.tps = [{rank := 0, tid := 5621}] from rfl,
    show initGoal_5621.ts = 5621 from rfl,
    show initGoal_5621.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 5621 = initSM 5621 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5621
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 5621 = initPM 5621 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5621
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l12ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := l12_zigzag_moe_weight5621_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8508)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16102)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16110)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMn_red_sm8508 initSM, l12ZMn_red_pm16102 initPM, l12ZMn_red_pm16110 initPM]
    exact hAttention
  rw [l12ZMn_red_sm5622 initSM, l12ZMn_red_pm9818 initPM, l12ZMn_red_pm9819 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L21 shared RMSNorm relation from the exact L20 graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem l12_zigzag_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l12ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L21 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem l12_zigzag_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8523)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13932)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l12_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l12ZMn_red_sm8523 initSM, l12ZMn_red_pm13932 initPM, l12ZMn_red_pm13933 initPM]
  exact hNorm

/-- The L21 scalar gate is closed from the same L12 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem l12_zigzag_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9848)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9849)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := l12_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l12_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
