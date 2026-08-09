/- Canonical Goal 1, layer 16: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.L16ZigzagMoEResidualGate
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

private def l16ZMnSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5944],
    outs := [8742, 8746], params := [2] }
private def l16ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10738],
    outs := [16294, 16298], params := [2] }
private def l16ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10739],
    outs := [16302, 16306], params := [2] }
private def l16ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8742, 5945], outs := [5946] }
private def l16ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16294, 5945], outs := [10742] }
private def l16ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16302, 5945], outs := [10743] }
private def l16ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5946],
    outs := [8753, 8757, 8761, 8765, 8769], params := [5] }
private def l16ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10742],
    outs := [15412, 14628, 14638, 14652, 14664], params := [5] }
private def l16ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10743],
    outs := [15414, 14629, 14639, 14653, 14665], params := [5] }

private theorem l16ZMn_red_sm8742 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8742 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5944 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 722 l16ZMnSmRef2
    5944 8742 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5944 [8742, 8746] 2 rfl 8742
    (by decide)

private theorem l16ZMn_red_pm16294 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16294 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10738 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1583 l16ZMnPmRef20
    10738 16294 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10738 [16294, 16298] 2 rfl 16294
    (by decide)

private theorem l16ZMn_red_pm16302 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16302 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10739 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1584 l16ZMnPmRef21
    10739 16302 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10739 [16302, 16306] 2 rfl 16302
    (by decide)

private theorem l16ZMn_red_sm5946 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5946 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8742)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5945) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 723 l16ZMnSmRms
    8742 5945 5946 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8742 5945 5946

private theorem l16ZMn_red_pm10742 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10742 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16294)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5945) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1585 l16ZMnPmRms0
    16294 5945 10742 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16294 5945 10742

private theorem l16ZMn_red_pm10743 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10743 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16302)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5945) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1586 l16ZMnPmRms1
    16302 5945 10743 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16302 5945 10743

private theorem l16ZMn_red_sm8757 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8757 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5946 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 724 l16ZMnSmRef5
    5946 8757 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5946 [8753, 8757, 8761, 8765, 8769]
    5 rfl 8757 (by decide)

private theorem l16ZMn_red_pm14628 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14628 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10742 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1587 l16ZMnPmRef50
    10742 14628 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10742
    [15412, 14628, 14638, 14652, 14664] 5 rfl 14628 (by decide)

private theorem l16ZMn_red_pm14629 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14629 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10743 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1588 l16ZMnPmRef51
    10743 14629 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10743
    [15414, 14629, 14639, 14653, 14665] 5 rfl 14629 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 5945. -/
theorem l16_zigzag_moe_weight5945_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5945 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5945 := by
  have h := hInit initGoal_5945 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5945 pm_goal_1.numRanks _ rfl,
    show initGoal_5945.tps = [{rank := 0, tid := 5945}] from rfl,
    show initGoal_5945.ts = 5945 from rfl,
    show initGoal_5945.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 5945 = initSM 5945 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5945
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 5945 = initPM 5945 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5945
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l16ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := l16_zigzag_moe_weight5945_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16294)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16302)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMn_red_sm8742 initSM, l16ZMn_red_pm16294 initPM, l16ZMn_red_pm16302 initPM]
    exact hAttention
  rw [l16ZMn_red_sm5946 initSM, l16ZMn_red_pm10742 initPM, l16ZMn_red_pm10743 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L16 shared RMSNorm relation from the exact L16 attention-residual graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem l16_zigzag_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l16ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L16 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem l16_zigzag_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8757)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14628)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14629)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l16_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l16ZMn_red_sm8757 initSM, l16ZMn_red_pm14628 initPM, l16ZMn_red_pm14629 initPM]
  exact hNorm

/-- The L16 scalar gate is closed from the same L16 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem l16_zigzag_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5960)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10772)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10773)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := l16_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l16_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
