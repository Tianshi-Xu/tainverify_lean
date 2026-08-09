/- Canonical Goal 1, layer 19: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.L19ZigzagMoEResidualGate
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

private def l19ZMnSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6106],
    outs := [8859, 8863], params := [2] }
private def l19ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11200],
    outs := [16390, 16394], params := [2] }
private def l19ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11201],
    outs := [16398, 16402], params := [2] }
private def l19ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8859, 6107], outs := [6108] }
private def l19ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16390, 6107], outs := [11204] }
private def l19ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16398, 6107], outs := [11205] }
private def l19ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6108],
    outs := [8870, 8874, 8878, 8882, 8886], params := [5] }
private def l19ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11204],
    outs := [15424, 14976, 14986, 15000, 15012], params := [5] }
private def l19ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11205],
    outs := [15426, 14977, 14987, 15001, 15013], params := [5] }

private theorem l19ZMn_red_sm8859 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8859 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6106 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 827 l19ZMnSmRef2
    6106 8859 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6106 [8859, 8863] 2 rfl 8859
    (by decide)

private theorem l19ZMn_red_pm16390 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16390 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11200 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1811 l19ZMnPmRef20
    11200 16390 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11200 [16390, 16394] 2 rfl 16390
    (by decide)

private theorem l19ZMn_red_pm16398 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16398 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11201 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1812 l19ZMnPmRef21
    11201 16398 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11201 [16398, 16402] 2 rfl 16398
    (by decide)

private theorem l19ZMn_red_sm6108 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6108 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8859)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6107) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 828 l19ZMnSmRms
    8859 6107 6108 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8859 6107 6108

private theorem l19ZMn_red_pm11204 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11204 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16390)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6107) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1813 l19ZMnPmRms0
    16390 6107 11204 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16390 6107 11204

private theorem l19ZMn_red_pm11205 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11205 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16398)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6107) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1814 l19ZMnPmRms1
    16398 6107 11205 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16398 6107 11205

private theorem l19ZMn_red_sm8874 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8874 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6108 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 829 l19ZMnSmRef5
    6108 8874 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6108 [8870, 8874, 8878, 8882, 8886]
    5 rfl 8874 (by decide)

private theorem l19ZMn_red_pm14976 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14976 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11204 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1815 l19ZMnPmRef50
    11204 14976 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11204
    [15424, 14976, 14986, 15000, 15012] 5 rfl 14976 (by decide)

private theorem l19ZMn_red_pm14977 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14977 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11205 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1816 l19ZMnPmRef51
    11205 14977 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11205
    [15426, 14977, 14987, 15001, 15013] 5 rfl 14977 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 6107. -/
theorem l19_zigzag_moe_weight6107_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6107 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6107 := by
  have h := hInit initGoal_6107 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6107 pm_goal_1.numRanks _ rfl,
    show initGoal_6107.tps = [{rank := 0, tid := 6107}] from rfl,
    show initGoal_6107.ts = 6107 from rfl,
    show initGoal_6107.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 6107 = initSM 6107 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6107
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 6107 = initPM 6107 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6107
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l19ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6108)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11204)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11205)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := l19_zigzag_moe_weight6107_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8859)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16390)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16398)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMn_red_sm8859 initSM, l19ZMn_red_pm16390 initPM, l19ZMn_red_pm16398 initPM]
    exact hAttention
  rw [l19ZMn_red_sm6108 initSM, l19ZMn_red_pm11204 initPM, l19ZMn_red_pm11205 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L19 shared RMSNorm relation from the exact L19 attention-residual graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem l19_zigzag_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6108)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11204)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11205)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l19ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L19 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem l19_zigzag_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8874)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14976)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l19_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l19ZMn_red_sm8874 initSM, l19ZMn_red_pm14976 initPM, l19ZMn_red_pm14977 initPM]
  exact hNorm

/-- The L19 scalar gate is closed from the same L19 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem l19_zigzag_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11235)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := l19_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l19_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
