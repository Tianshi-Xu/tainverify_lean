/- Canonical Goal 1, layer 18: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.L18ZigzagMoEResidualGate
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

private def l18ZMnSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6052],
    outs := [8820, 8824], params := [2] }
private def l18ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11046],
    outs := [16358, 16362], params := [2] }
private def l18ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11047],
    outs := [16366, 16370], params := [2] }
private def l18ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8820, 6053], outs := [6054] }
private def l18ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16358, 6053], outs := [11050] }
private def l18ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16366, 6053], outs := [11051] }
private def l18ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6054],
    outs := [8831, 8835, 8839, 8843, 8847], params := [5] }
private def l18ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11050],
    outs := [15420, 14860, 14870, 14884, 14896], params := [5] }
private def l18ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11051],
    outs := [15422, 14861, 14871, 14885, 14897], params := [5] }

private theorem l18ZMn_red_sm8820 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8820 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6052 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 792 l18ZMnSmRef2
    6052 8820 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6052 [8820, 8824] 2 rfl 8820
    (by decide)

private theorem l18ZMn_red_pm16358 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16358 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11046 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1735 l18ZMnPmRef20
    11046 16358 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11046 [16358, 16362] 2 rfl 16358
    (by decide)

private theorem l18ZMn_red_pm16366 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16366 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11047 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1736 l18ZMnPmRef21
    11047 16366 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11047 [16366, 16370] 2 rfl 16366
    (by decide)

private theorem l18ZMn_red_sm6054 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6054 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8820)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6053) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 793 l18ZMnSmRms
    8820 6053 6054 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8820 6053 6054

private theorem l18ZMn_red_pm11050 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11050 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16358)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6053) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1737 l18ZMnPmRms0
    16358 6053 11050 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16358 6053 11050

private theorem l18ZMn_red_pm11051 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11051 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16366)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6053) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1738 l18ZMnPmRms1
    16366 6053 11051 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16366 6053 11051

private theorem l18ZMn_red_sm8835 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8835 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6054 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 794 l18ZMnSmRef5
    6054 8835 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6054 [8831, 8835, 8839, 8843, 8847]
    5 rfl 8835 (by decide)

private theorem l18ZMn_red_pm14860 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14860 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11050 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1739 l18ZMnPmRef50
    11050 14860 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11050
    [15420, 14860, 14870, 14884, 14896] 5 rfl 14860 (by decide)

private theorem l18ZMn_red_pm14861 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14861 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11051 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1740 l18ZMnPmRef51
    11051 14861 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11051
    [15422, 14861, 14871, 14885, 14897] 5 rfl 14861 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 6053. -/
theorem l18_zigzag_moe_weight6053_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6053 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6053 := by
  have h := hInit initGoal_6053 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6053 pm_goal_1.numRanks _ rfl,
    show initGoal_6053.tps = [{rank := 0, tid := 6053}] from rfl,
    show initGoal_6053.ts = 6053 from rfl,
    show initGoal_6053.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 6053 = initSM 6053 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6053
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 6053 = initPM 6053 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6053
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l18ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := l18_zigzag_moe_weight6053_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8820)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16358)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16366)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMn_red_sm8820 initSM, l18ZMn_red_pm16358 initPM, l18ZMn_red_pm16366 initPM]
    exact hAttention
  rw [l18ZMn_red_sm6054 initSM, l18ZMn_red_pm11050 initPM, l18ZMn_red_pm11051 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L18 shared RMSNorm relation from the exact L18 attention-residual graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem l18_zigzag_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l18ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L18 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem l18_zigzag_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8835)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14860)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14861)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l18_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l18ZMn_red_sm8835 initSM, l18ZMn_red_pm14860 initPM, l18ZMn_red_pm14861 initPM]
  exact hNorm

/-- The L18 scalar gate is closed from the same L18 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem l18_zigzag_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6068)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11080)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11081)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := l18_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l18_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
