/- Canonical Goal 1, layer 12: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.L12Block2ZigzagMoEResidualGate
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

private def l12B2ZMnSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5674],
    outs := [8547, 8551], params := [2] }
private def l12B2ZMnPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9968],
    outs := [16134, 16138], params := [2] }
private def l12B2ZMnPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9969],
    outs := [16142, 16146], params := [2] }
private def l12B2ZMnSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8547, 5675], outs := [5676] }
private def l12B2ZMnPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16134, 5675], outs := [9972] }
private def l12B2ZMnPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16142, 5675], outs := [9973] }
private def l12B2ZMnSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5676],
    outs := [8558, 8562, 8566, 8570, 8574], params := [5] }
private def l12B2ZMnPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9972],
    outs := [15392, 14048, 14058, 14072, 14084], params := [5] }
private def l12B2ZMnPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9973],
    outs := [15394, 14049, 14059, 14073, 14085], params := [5] }

private theorem l12B2ZMn_red_sm8547 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8547 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5674 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 547 l12B2ZMnSmRef2
    5674 8547 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMnSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5674 [8547, 8551] 2 rfl 8547
    (by decide)

private theorem l12B2ZMn_red_pm16134 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16134 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9968 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1203 l12B2ZMnPmRef20
    9968 16134 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMnPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9968 [16134, 16138] 2 rfl 16134
    (by decide)

private theorem l12B2ZMn_red_pm16142 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16142 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9969 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1204 l12B2ZMnPmRef21
    9969 16142 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMnPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9969 [16142, 16146] 2 rfl 16142
    (by decide)

private theorem l12B2ZMn_red_sm5676 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5676 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8547)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5675) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 548 l12B2ZMnSmRms
    8547 5675 5676 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMnSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8547 5675 5676

private theorem l12B2ZMn_red_pm9972 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9972 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16134)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5675) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1205 l12B2ZMnPmRms0
    16134 5675 9972 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMnPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16134 5675 9972

private theorem l12B2ZMn_red_pm9973 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9973 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16142)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5675) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1206 l12B2ZMnPmRms1
    16142 5675 9973 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMnPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16142 5675 9973

private theorem l12B2ZMn_red_sm8562 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8562 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5676 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 549 l12B2ZMnSmRef5
    5676 8562 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMnSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5676 [8558, 8562, 8566, 8570, 8574]
    5 rfl 8562 (by decide)

private theorem l12B2ZMn_red_pm14048 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14048 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9972 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1207 l12B2ZMnPmRef50
    9972 14048 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMnPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9972
    [15392, 14048, 14058, 14072, 14084] 5 rfl 14048 (by decide)

private theorem l12B2ZMn_red_pm14049 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14049 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9973 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1208 l12B2ZMnPmRef51
    9973 14049 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMnPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9973
    [15394, 14049, 14059, 14073, 14085] 5 rfl 14049 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 5675. -/
theorem l12b2_zigzag_moe_weight5675_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5675 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5675 := by
  have h := hInit initGoal_5675 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5675 pm_goal_1.numRanks _ rfl,
    show initGoal_5675.tps = [{rank := 0, tid := 5675}] from rfl,
    show initGoal_5675.ts = 5675 from rfl,
    show initGoal_5675.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 5675 = initSM 5675 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5675
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 5675 = initPM 5675 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5675
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem l12B2ZMn_norm_of_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5676)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9972)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := l12b2_zigzag_moe_weight5675_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8547)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16134)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16142)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMn_red_sm8547 initSM, l12B2ZMn_red_pm16134 initPM, l12B2ZMn_red_pm16142 initPM]
    exact hAttention
  rw [l12B2ZMn_red_sm5676 initSM, l12B2ZMn_red_pm9972 initPM, l12B2ZMn_red_pm9973 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L21 shared RMSNorm relation from the exact L20 graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem l12b2_zigzag_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5676)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9972)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l12B2ZMn_norm_of_attention initSM initPM hInit hAttention

/-- The exact L21 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem l12b2_zigzag_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14048)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14049)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l12b2_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l12B2ZMn_red_sm8562 initSM, l12B2ZMn_red_pm14048 initPM, l12B2ZMn_red_pm14049 initPM]
  exact hNorm

/-- The L21 scalar gate is closed from the same L12 block-2 attention residual contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem l12b2_zigzag_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5690)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10002)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10003)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := l12b2_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l12b2_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
