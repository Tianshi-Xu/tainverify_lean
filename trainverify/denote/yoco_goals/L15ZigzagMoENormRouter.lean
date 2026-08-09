/- Canonical Goal 1, layer 15: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.L15ZigzagMoEResidualGate
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

private def l15ZMnSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5890],
    outs := [8703, 8707], params := [2] }
private def l15ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10584],
    outs := [16262, 16266], params := [2] }
private def l15ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10585],
    outs := [16270, 16274], params := [2] }
private def l15ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8703, 5891], outs := [5892] }
private def l15ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16262, 5891], outs := [10588] }
private def l15ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16270, 5891], outs := [10589] }
private def l15ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5892],
    outs := [8714, 8718, 8722, 8726, 8730], params := [5] }
private def l15ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10588],
    outs := [15408, 14512, 14522, 14536, 14548], params := [5] }
private def l15ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10589],
    outs := [15410, 14513, 14523, 14537, 14549], params := [5] }

private theorem l15ZMn_red_sm8703 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8703 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5890 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 687 l15ZMnSmRef2
    5890 8703 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5890 [8703, 8707] 2 rfl 8703
    (by decide)

private theorem l15ZMn_red_pm16262 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16262 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10584 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1507 l15ZMnPmRef20
    10584 16262 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10584 [16262, 16266] 2 rfl 16262
    (by decide)

private theorem l15ZMn_red_pm16270 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16270 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10585 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1508 l15ZMnPmRef21
    10585 16270 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10585 [16270, 16274] 2 rfl 16270
    (by decide)

private theorem l15ZMn_red_sm5892 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5892 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8703)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5891) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 688 l15ZMnSmRms
    8703 5891 5892 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8703 5891 5892

private theorem l15ZMn_red_pm10588 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10588 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16262)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5891) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1509 l15ZMnPmRms0
    16262 5891 10588 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16262 5891 10588

private theorem l15ZMn_red_pm10589 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10589 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16270)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5891) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1510 l15ZMnPmRms1
    16270 5891 10589 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16270 5891 10589

private theorem l15ZMn_red_sm8718 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8718 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5892 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 689 l15ZMnSmRef5
    5892 8718 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5892 [8714, 8718, 8722, 8726, 8730]
    5 rfl 8718 (by decide)

private theorem l15ZMn_red_pm14512 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14512 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10588 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1511 l15ZMnPmRef50
    10588 14512 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10588
    [15408, 14512, 14522, 14536, 14548] 5 rfl 14512 (by decide)

private theorem l15ZMn_red_pm14513 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14513 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10589 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1512 l15ZMnPmRef51
    10589 14513 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10589
    [15410, 14513, 14523, 14537, 14549] 5 rfl 14513 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 5891. -/
theorem l15_zigzag_moe_weight5891_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5891 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5891 := by
  have h := hInit initGoal_5891 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5891 pm_goal_1.numRanks _ rfl,
    show initGoal_5891.tps = [{rank := 0, tid := 5891}] from rfl,
    show initGoal_5891.ts = 5891 from rfl,
    show initGoal_5891.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 5891 = initSM 5891 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5891
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 5891 = initPM 5891 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5891
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l15ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10584)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10589)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := l15_zigzag_moe_weight5891_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8703)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16262)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16270)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMn_red_sm8703 initSM, l15ZMn_red_pm16262 initPM, l15ZMn_red_pm16270 initPM]
    exact hAttention
  rw [l15ZMn_red_sm5892 initSM, l15ZMn_red_pm10588 initPM, l15ZMn_red_pm10589 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L15 shared RMSNorm relation from the exact L15 attention-residual graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem l15_zigzag_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10584)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10589)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l15ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L15 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem l15_zigzag_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10584)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8718)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14513)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l15_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l15ZMn_red_sm8718 initSM, l15ZMn_red_pm14512 initPM, l15ZMn_red_pm14513 initPM]
  exact hNorm

/-- The L15 scalar gate is closed from the same L15 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem l15_zigzag_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10584)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5906)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10618)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10619)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := l15_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l15_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
