/- Canonical Goal 1, layer 17: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.L17ZigzagMoEResidualGate
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

private def l17ZMnSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5998],
    outs := [8781, 8785], params := [2] }
private def l17ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10892],
    outs := [16326, 16330], params := [2] }
private def l17ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10893],
    outs := [16334, 16338], params := [2] }
private def l17ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8781, 5999], outs := [6000] }
private def l17ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16326, 5999], outs := [10896] }
private def l17ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16334, 5999], outs := [10897] }
private def l17ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6000],
    outs := [8792, 8796, 8800, 8804, 8808], params := [5] }
private def l17ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10896],
    outs := [15416, 14744, 14754, 14768, 14780], params := [5] }
private def l17ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10897],
    outs := [15418, 14745, 14755, 14769, 14781], params := [5] }

private theorem l17ZMn_red_sm8781 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8781 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5998 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 757 l17ZMnSmRef2
    5998 8781 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5998 [8781, 8785] 2 rfl 8781
    (by decide)

private theorem l17ZMn_red_pm16326 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16326 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10892 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1659 l17ZMnPmRef20
    10892 16326 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10892 [16326, 16330] 2 rfl 16326
    (by decide)

private theorem l17ZMn_red_pm16334 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16334 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10893 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1660 l17ZMnPmRef21
    10893 16334 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10893 [16334, 16338] 2 rfl 16334
    (by decide)

private theorem l17ZMn_red_sm6000 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6000 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8781)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5999) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 758 l17ZMnSmRms
    8781 5999 6000 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8781 5999 6000

private theorem l17ZMn_red_pm10896 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10896 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16326)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5999) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1661 l17ZMnPmRms0
    16326 5999 10896 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16326 5999 10896

private theorem l17ZMn_red_pm10897 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10897 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16334)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5999) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1662 l17ZMnPmRms1
    16334 5999 10897 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16334 5999 10897

private theorem l17ZMn_red_sm8796 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8796 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6000 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 759 l17ZMnSmRef5
    6000 8796 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6000 [8792, 8796, 8800, 8804, 8808]
    5 rfl 8796 (by decide)

private theorem l17ZMn_red_pm14744 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14744 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10896 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1663 l17ZMnPmRef50
    10896 14744 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10896
    [15416, 14744, 14754, 14768, 14780] 5 rfl 14744 (by decide)

private theorem l17ZMn_red_pm14745 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14745 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10897 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1664 l17ZMnPmRef51
    10897 14745 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10897
    [15418, 14745, 14755, 14769, 14781] 5 rfl 14745 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 5999. -/
theorem l17_zigzag_moe_weight5999_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5999 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5999 := by
  have h := hInit initGoal_5999 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5999 pm_goal_1.numRanks _ rfl,
    show initGoal_5999.tps = [{rank := 0, tid := 5999}] from rfl,
    show initGoal_5999.ts = 5999 from rfl,
    show initGoal_5999.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 5999 = initSM 5999 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5999
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 5999 = initPM 5999 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5999
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l17ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10893)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := l17_zigzag_moe_weight5999_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8781)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16326)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16334)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMn_red_sm8781 initSM, l17ZMn_red_pm16326 initPM, l17ZMn_red_pm16334 initPM]
    exact hAttention
  rw [l17ZMn_red_sm6000 initSM, l17ZMn_red_pm10896 initPM, l17ZMn_red_pm10897 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L17 shared RMSNorm relation from the exact L17 attention-residual graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem l17_zigzag_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10893)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l17ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L17 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem l17_zigzag_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10893)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8796)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14744)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14745)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l17_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l17ZMn_red_sm8796 initSM, l17ZMn_red_pm14744 initPM, l17ZMn_red_pm14745 initPM]
  exact hNorm

/-- The L17 scalar gate is closed from the same L17 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem l17_zigzag_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10893)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6014)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10926)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10927)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := l17_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l17_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
