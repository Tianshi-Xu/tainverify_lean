/- Canonical Goal 1 cache layer: shared RMSNorm and expert activation input. -/
import denote.yoco_goals.CanonicalKVCacheResidualGate
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

private def cKVCnrSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5562],
    outs := [8337, 8341], params := [2] }
private def cKVCnrPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9632],
    outs := [15806, 15810], params := [2] }
private def cKVCnrPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9633],
    outs := [15814, 15818], params := [2] }
private def cKVCnrSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8337, 5563], outs := [5564] }
private def cKVCnrPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15806, 5563], outs := [9636] }
private def cKVCnrPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15814, 5563], outs := [9637] }
private def cKVCnrSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5564],
    outs := [8348, 8352, 8356, 8360, 8364], params := [5] }
private def cKVCnrPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9636],
    outs := [15384, 13796, 13806, 13820, 13832], params := [5] }
private def cKVCnrPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9637],
    outs := [15386, 13797, 13807, 13821, 13833], params := [5] }

private theorem cKVCnr_red_sm8337 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8337 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5562 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 445 cKVCnrSmResidualRef
    5562 8337 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCnrSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5562 [8337, 8341] 2 rfl 8337
    (by decide)

private theorem cKVCnr_red_pm15806 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15806 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9632 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 987 cKVCnrPmResidualRef0
    9632 15806 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCnrPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9632 [15806, 15810] 2 rfl 15806
    (by decide)

private theorem cKVCnr_red_pm15814 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15814 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9633 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 988 cKVCnrPmResidualRef1
    9633 15814 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCnrPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9633 [15814, 15818] 2 rfl 15814
    (by decide)

private theorem cKVCnr_red_sm5564 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5564 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8337)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 446 cKVCnrSmRms
    8337 5563 5564 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCnrSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8337 5563 5564

private theorem cKVCnr_red_pm9636 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9636 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15806)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 989 cKVCnrPmRms0
    15806 5563 9636 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCnrPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15806 5563 9636

private theorem cKVCnr_red_pm9637 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9637 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15814)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 990 cKVCnrPmRms1
    15814 5563 9637 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCnrPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15814 5563 9637

private theorem cKVCnr_red_sm8352 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8352 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 447 cKVCnrSmNormRef
    5564 8352 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCnrSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564 [8348, 8352, 8356, 8360, 8364]
    5 rfl 8352 (by decide)

private theorem cKVCnr_red_pm13796 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13796 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 991 cKVCnrPmNormRef0
    9636 13796 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCnrPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636
    [15384, 13796, 13806, 13820, 13832] 5 rfl 13796 (by decide)

private theorem cKVCnr_red_pm13797 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13797 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 992 cKVCnrPmNormRef1
    9637 13797 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCnrPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637
    [15386, 13797, 13807, 13821, 13833] 5 rfl 13797 (by decide)

private theorem cKVCnr_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5563 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5563 := by
  have h := hInit initGoal_5563 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5563 pm_goal_1.numRanks _ rfl,
    show initGoal_5563.tps = [{rank := 0, tid := 5563}] from rfl,
    show initGoal_5563.ts = 5563 from rfl,
    show initGoal_5563.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5563
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5563
      (by native_decide) (by native_decide)]
  exact hval

/-- The real cache-layer RMSNorm is closed from the preceding attention output.
Its shared weight relation is derived from the full init-goal contract. -/
theorem canonical_kv_cache_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5564)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9637)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8337)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15806)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15814)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCnr_red_sm8337 initSM, cKVCnr_red_pm15806 initPM,
      cKVCnr_red_pm15814 initPM]
    exact hAttention
  have hWeight := cKVCnr_weight_bridge initSM initPM hInit
  rw [cKVCnr_red_sm5564 initSM, cKVCnr_red_pm9636 initPM,
    cKVCnr_red_pm9637 initPM, hWeight]
  exact Zigzag2Rel.rms_norm 2048 1024 hRef (by decide) (by decide) rfl

/-- The exact expert activation inputs are aliases of the cache-layer RMSNorm output;
no computed norm or activation relation is required from the caller. -/
theorem canonical_kv_cache_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8352)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13796)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13797)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := canonical_kv_cache_norm_from_attention_output initSM initPM hInit hAttention
  rw [cKVCnr_red_sm8352 initSM, cKVCnr_red_pm13796 initPM,
    cKVCnr_red_pm13797 initPM]
  exact hNorm

/-- The cache scalar gate is closed from the same preceding attention output.  Its
normalized input is computed internally by the real RMSNorm nodes. -/
theorem canonical_kv_cache_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9667)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hNorm := canonical_kv_cache_norm_from_attention_output initSM initPM hInit hAttention
  exact canonical_kv_cache_gate_from_norm_input initSM initPM hPM hInit hNorm

#print axioms canonical_kv_cache_norm_from_attention_output
#print axioms canonical_kv_cache_activation_from_attention_output
#print axioms canonical_kv_cache_gate_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
