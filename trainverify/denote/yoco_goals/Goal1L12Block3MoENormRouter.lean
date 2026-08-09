/- Canonical Goal 1, layer 12: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.Goal1L12Block3MoEResidualGate
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
  { rank := 0, op := "OpName.FW_multiref", ins := [5728],
    outs := [8586, 8590], params := [2] }
private def l12ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10122],
    outs := [16166, 16170], params := [2] }
private def l12ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10123],
    outs := [16174, 16178], params := [2] }
private def l12ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8586, 5729], outs := [5730] }
private def l12ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16166, 5729], outs := [10126] }
private def l12ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16174, 5729], outs := [10127] }
private def l12ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5730],
    outs := [8597, 8601, 8605, 8609, 8613], params := [5] }
private def l12ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10126],
    outs := [15396, 14164, 14174, 14188, 14200], params := [5] }
private def l12ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10127],
    outs := [15398, 14165, 14175, 14189, 14201], params := [5] }

private theorem l12ZMn_red_sm8586 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8586 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5728 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 582 l12ZMnSmRef2
    5728 8586 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5728 [8586, 8590] 2 rfl 8586
    (by decide)

private theorem l12ZMn_red_pm16166 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16166 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10122 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1279 l12ZMnPmRef20
    10122 16166 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10122 [16166, 16170] 2 rfl 16166
    (by decide)

private theorem l12ZMn_red_pm16174 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16174 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10123 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1280 l12ZMnPmRef21
    10123 16174 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10123 [16174, 16178] 2 rfl 16174
    (by decide)

private theorem l12ZMn_red_sm5730 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5730 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8586)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5729) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 583 l12ZMnSmRms
    8586 5729 5730 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8586 5729 5730

private theorem l12ZMn_red_pm10126 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10126 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16166)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5729) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1281 l12ZMnPmRms0
    16166 5729 10126 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16166 5729 10126

private theorem l12ZMn_red_pm10127 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10127 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16174)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5729) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1282 l12ZMnPmRms1
    16174 5729 10127 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16174 5729 10127

private theorem l12ZMn_red_sm8601 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8601 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5730 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 584 l12ZMnSmRef5
    5730 8601 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5730 [8597, 8601, 8605, 8609, 8613]
    5 rfl 8601 (by decide)

private theorem l12ZMn_red_pm14164 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14164 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10126 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1283 l12ZMnPmRef50
    10126 14164 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10126
    [15396, 14164, 14174, 14188, 14200] 5 rfl 14164 (by decide)

private theorem l12ZMn_red_pm14165 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14165 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10127 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1284 l12ZMnPmRef51
    10127 14165 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10127
    [15398, 14165, 14175, 14189, 14201] 5 rfl 14165 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 5729. -/
theorem goal1_l12_block3_moe_weight5729_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5729 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5729 := by
  have h := hInit initGoal_5729 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5729 pm_goal_1.numRanks _ rfl,
    show initGoal_5729.tps = [{rank := 0, tid := 5729}] from rfl,
    show initGoal_5729.ts = 5729 from rfl,
    show initGoal_5729.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 5729 = initSM 5729 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5729
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 5729 = initPM 5729 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5729
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l12ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5728)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5730)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10126)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10127)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := goal1_l12_block3_moe_weight5729_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8586)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16166)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16174)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMn_red_sm8586 initSM, l12ZMn_red_pm16166 initPM, l12ZMn_red_pm16174 initPM]
    exact hAttention
  rw [l12ZMn_red_sm5730 initSM, l12ZMn_red_pm10126 initPM, l12ZMn_red_pm10127 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L21 shared RMSNorm relation from the exact L20 graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem goal1_l12_block3_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5728)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5730)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10126)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10127)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l12ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L21 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem goal1_l12_block3_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5728)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8601)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14164)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14165)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := goal1_l12_block3_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l12ZMn_red_sm8601 initSM, l12ZMn_red_pm14164 initPM, l12ZMn_red_pm14165 initPM]
  exact hNorm

/-- The L21 scalar gate is closed from the same L12 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem goal1_l12_block3_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5728)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5744)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10156)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10157)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := goal1_l12_block3_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact goal1_l12_block3_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
