/- Canonical Goal 1, layer 13: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.L13ZigzagMoEResidualGate
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

private def l13ZMnSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5782],
    outs := [8625, 8629], params := [2] }
private def l13ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10276],
    outs := [16198, 16202], params := [2] }
private def l13ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10277],
    outs := [16206, 16210], params := [2] }
private def l13ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8625, 5783], outs := [5784] }
private def l13ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16198, 5783], outs := [10280] }
private def l13ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16206, 5783], outs := [10281] }
private def l13ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5784],
    outs := [8636, 8640, 8644, 8648, 8652], params := [5] }
private def l13ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10280],
    outs := [15400, 14280, 14290, 14304, 14316], params := [5] }
private def l13ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10281],
    outs := [15402, 14281, 14291, 14305, 14317], params := [5] }

private theorem l13ZMn_red_sm8625 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8625 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5782 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 617 l13ZMnSmRef2
    5782 8625 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5782 [8625, 8629] 2 rfl 8625
    (by decide)

private theorem l13ZMn_red_pm16198 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16198 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10276 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1355 l13ZMnPmRef20
    10276 16198 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10276 [16198, 16202] 2 rfl 16198
    (by decide)

private theorem l13ZMn_red_pm16206 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16206 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10277 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1356 l13ZMnPmRef21
    10277 16206 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10277 [16206, 16210] 2 rfl 16206
    (by decide)

private theorem l13ZMn_red_sm5784 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5784 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8625)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5783) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 618 l13ZMnSmRms
    8625 5783 5784 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8625 5783 5784

private theorem l13ZMn_red_pm10280 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10280 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16198)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5783) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1357 l13ZMnPmRms0
    16198 5783 10280 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16198 5783 10280

private theorem l13ZMn_red_pm10281 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10281 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16206)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5783) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1358 l13ZMnPmRms1
    16206 5783 10281 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16206 5783 10281

private theorem l13ZMn_red_sm8640 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8640 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5784 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 619 l13ZMnSmRef5
    5784 8640 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5784 [8636, 8640, 8644, 8648, 8652]
    5 rfl 8640 (by decide)

private theorem l13ZMn_red_pm14280 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14280 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10280 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1359 l13ZMnPmRef50
    10280 14280 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10280
    [15400, 14280, 14290, 14304, 14316] 5 rfl 14280 (by decide)

private theorem l13ZMn_red_pm14281 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14281 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10281 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1360 l13ZMnPmRef51
    10281 14281 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10281
    [15402, 14281, 14291, 14305, 14317] 5 rfl 14281 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 5783. -/
theorem l13_zigzag_moe_weight5783_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5783 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5783 := by
  have h := hInit initGoal_5783 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5783 pm_goal_1.numRanks _ rfl,
    show initGoal_5783.tps = [{rank := 0, tid := 5783}] from rfl,
    show initGoal_5783.ts = 5783 from rfl,
    show initGoal_5783.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 5783 = initSM 5783 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5783
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 5783 = initPM 5783 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5783
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l13ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10277)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5784)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10280)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10281)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := l13_zigzag_moe_weight5783_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8625)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16198)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMn_red_sm8625 initSM, l13ZMn_red_pm16198 initPM, l13ZMn_red_pm16206 initPM]
    exact hAttention
  rw [l13ZMn_red_sm5784 initSM, l13ZMn_red_pm10280 initPM, l13ZMn_red_pm10281 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L13 shared RMSNorm relation from the exact L13 attention-residual graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem l13_zigzag_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10277)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5784)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10280)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10281)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l13ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L13 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem l13_zigzag_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10277)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8640)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14280)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14281)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l13_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l13ZMn_red_sm8640 initSM, l13ZMn_red_pm14280 initPM, l13ZMn_red_pm14281 initPM]
  exact hNorm

/-- The L13 scalar gate is closed from the same L13 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem l13_zigzag_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10277)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5798)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10310)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10311)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := l13_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l13_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
