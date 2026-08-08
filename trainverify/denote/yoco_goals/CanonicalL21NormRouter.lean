/- Canonical Goal 1, layer 21: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.CanonicalL21ResidualGate
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

private def cL21nSmRef2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6160],
    outs := [8898, 8902], params := [2] }
private def cL21nPmRef20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11354],
    outs := [16422, 16426], params := [2] }
private def cL21nPmRef21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11355],
    outs := [16430, 16434], params := [2] }
private def cL21nSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8898, 6161], outs := [6162] }
private def cL21nPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16422, 6161], outs := [11358] }
private def cL21nPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16430, 6161], outs := [11359] }
private def cL21nSmRef5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6162],
    outs := [8909, 8913, 8917, 8921, 8925], params := [5] }
private def cL21nPmRef50 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11358],
    outs := [15428, 15092, 15102, 15116, 15128], params := [5] }
private def cL21nPmRef51 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11359],
    outs := [15430, 15093, 15103, 15117, 15129], params := [5] }

private theorem cL21n_red_sm8898 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8898 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6160 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 862 cL21nSmRef2
    6160 8898 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21nSmRef2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6160 [8898, 8902] 2 rfl 8898
    (by decide)

private theorem cL21n_red_pm16422 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16422 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11354 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1887 cL21nPmRef20
    11354 16422 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21nPmRef20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11354 [16422, 16426] 2 rfl 16422
    (by decide)

private theorem cL21n_red_pm16430 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16430 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11355 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1888 cL21nPmRef21
    11355 16430 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21nPmRef21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11355 [16430, 16434] 2 rfl 16430
    (by decide)

private theorem cL21n_red_sm6162 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6162 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8898)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6161) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 863 cL21nSmRms
    8898 6161 6162 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21nSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8898 6161 6162

private theorem cL21n_red_pm11358 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11358 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16422)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6161) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1889 cL21nPmRms0
    16422 6161 11358 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21nPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16422 6161 11358

private theorem cL21n_red_pm11359 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11359 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16430)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6161) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1890 cL21nPmRms1
    16430 6161 11359 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21nPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16430 6161 11359

private theorem cL21n_red_sm8913 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8913 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6162 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 864 cL21nSmRef5
    6162 8913 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21nSmRef5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6162 [8909, 8913, 8917, 8921, 8925]
    5 rfl 8913 (by decide)

private theorem cL21n_red_pm15092 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15092 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11358 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1891 cL21nPmRef50
    11358 15092 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21nPmRef50
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11358
    [15428, 15092, 15102, 15116, 15128] 5 rfl 15092 (by decide)

private theorem cL21n_red_pm15093 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15093 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11359 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1892 cL21nPmRef51
    11359 15093 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21nPmRef51
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11359
    [15430, 15093, 15103, 15117, 15129] 5 rfl 15093 (by decide)

/-- The external init-goal contract closes the shared RMSNorm weight boundary;
the computed graphs do not rewrite tensor 6161. -/
theorem canonical_l21_weight6161_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6161 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6161 := by
  have h := hInit initGoal_6161 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6161 pm_goal_1.numRanks _ rfl,
    show initGoal_6161.tps = [{rank := 0, tid := 6161}] from rfl,
    show initGoal_6161.ts = 6161 from rfl,
    show initGoal_6161.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  have hsm : denoteGraphDistributedFaithful sm_goal_1 initSM 6161 = initSM 6161 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6161
      (by native_decide) (by native_decide)
  have hpm : denoteGraphDistributedFaithful pm_goal_1 initPM 6161 = initPM 6161 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6161
      (by native_decide) (by native_decide)
  rw [hsm, hpm]
  exact hval

private theorem cL21n_norm_of_layer20 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hLayer20 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11355)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6162)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11358)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11359)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hWeight := canonical_l21_weight6161_bridge initSM initPM hInit
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8898)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16422)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21n_red_sm8898 initSM, cL21n_red_pm16422 initPM, cL21n_red_pm16430 initPM]
    exact hLayer20
  rw [cL21n_red_sm6162 initSM, cL21n_red_pm11358 initPM, cL21n_red_pm11359 initPM,
    hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- Canonical L21 shared RMSNorm relation from the exact L20 graph outputs.
The RMSNorm weight equality and shape boundary are discharged internally from
`hInit`; no computed intermediate relation is exposed to the caller. -/
theorem canonical_l21_norm_from_layer20_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hLayer20 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11355)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6162)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11358)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11359)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact cL21n_norm_of_layer20 initSM initPM hInit hLayer20

/-- The exact L21 expert activation inputs are multiref aliases of the canonical
shared RMSNorm outputs. -/
theorem canonical_l21_activation_from_layer20_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hLayer20 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11355)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8913)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15092)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15093)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := canonical_l21_norm_from_layer20_output initSM initPM hInit hLayer20
  rw [cL21n_red_sm8913 initSM, cL21n_red_pm15092 initPM, cL21n_red_pm15093 initPM]
  exact hNorm

/-- The L21 scalar gate is closed from the same L20 output contract: its exact
`hNorm` input is obtained internally rather than required from the caller. -/
theorem canonical_l21_gate_from_layer20_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hLayer20 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11355)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6176)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11388)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11389)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := canonical_l21_norm_from_layer20_output initSM initPM hInit hLayer20
  exact canonical_l21_gate_from_norm_input initSM initPM hPM hInit hNorm

end
end TrainVerify.Denote.GeneratedPatterns
