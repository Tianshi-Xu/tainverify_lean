/- Canonical Goal 1, layer 14: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.L14ZigzagMoEResidualGate
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

private def l14ZMnSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5836],
    outs := [8664, 8668], params := [2] }
private def l14ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10430],
    outs := [16230, 16234], params := [2] }
private def l14ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10431],
    outs := [16238, 16242], params := [2] }
private def l14ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8664, 5837], outs := [5838] }
private def l14ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16230, 5837], outs := [10434] }
private def l14ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16238, 5837], outs := [10435] }
private def l14ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5838],
    outs := [8675, 8679, 8683, 8687, 8691], params := [5] }
private def l14ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10434],
    outs := [15404, 14396, 14406, 14420, 14432], params := [5] }
private def l14ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10435],
    outs := [15406, 14397, 14407, 14421, 14433], params := [5] }

private theorem l14ZMn_red_sm8664 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8664 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5836 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 652 l14ZMnSmRef2
    5836 8664 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5836 [8664, 8668] 2 rfl 8664
    (by decide)

private theorem l14ZMn_red_pm16230 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16230 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10430 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1431 l14ZMnPmRef20
    10430 16230 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10430 [16230, 16234] 2 rfl 16230
    (by decide)

private theorem l14ZMn_red_pm16238 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16238 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10431 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1432 l14ZMnPmRef21
    10431 16238 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10431 [16238, 16242] 2 rfl 16238
    (by decide)

private theorem l14ZMn_red_sm5838 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5838 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8664)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5837) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 653 l14ZMnSmRms
    8664 5837 5838 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8664 5837 5838

private theorem l14ZMn_red_pm10434 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10434 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16230)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5837) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1433 l14ZMnPmRms0
    16230 5837 10434 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16230 5837 10434

private theorem l14ZMn_red_pm10435 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10435 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16238)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5837) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1434 l14ZMnPmRms1
    16238 5837 10435 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16238 5837 10435

private theorem l14ZMn_red_sm8679 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8679 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5838 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 654 l14ZMnSmRef5
    5838 8679 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5838 [8675, 8679, 8683, 8687, 8691]
    5 rfl 8679 (by decide)

private theorem l14ZMn_red_pm14396 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14396 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10434 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1435 l14ZMnPmRef50
    10434 14396 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10434
    [15404, 14396, 14406, 14420, 14432] 5 rfl 14396 (by decide)

private theorem l14ZMn_red_pm14397 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14397 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10435 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1436 l14ZMnPmRef51
    10435 14397 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10435
    [15406, 14397, 14407, 14421, 14433] 5 rfl 14397 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 5837. -/
theorem l14_zigzag_moe_weight5837_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5837 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5837 := by
  have h := hInit initGoal_5837 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5837 pm_goal_1.numRanks _ rfl,
    show initGoal_5837.tps = [{rank := 0, tid := 5837}] from rfl,
    show initGoal_5837.ts = 5837 from rfl,
    show initGoal_5837.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 5837 = initSM 5837 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5837
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 5837 = initPM 5837 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5837
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l14ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10431)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5838)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10434)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10435)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := l14_zigzag_moe_weight5837_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8664)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16230)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16238)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMn_red_sm8664 initSM, l14ZMn_red_pm16230 initPM, l14ZMn_red_pm16238 initPM]
    exact hAttention
  rw [l14ZMn_red_sm5838 initSM, l14ZMn_red_pm10434 initPM, l14ZMn_red_pm10435 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L14 shared RMSNorm relation from the exact L14 attention-residual graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem l14_zigzag_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10431)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5838)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10434)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10435)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l14ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L14 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem l14_zigzag_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10431)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8679)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14396)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l14_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l14ZMn_red_sm8679 initSM, l14ZMn_red_pm14396 initPM, l14ZMn_red_pm14397 initPM]
  exact hNorm

/-- The L14 scalar gate is closed from the same L14 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem l14_zigzag_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10431)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5852)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10464)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10465)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := l14_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l14_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
