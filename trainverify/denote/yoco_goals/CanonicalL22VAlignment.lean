/- Canonical Goal 1, layer 22: align the faithful V graph values. -/
import denote.yoco_goals.CanonicalKVCacheComposition
import denote.yoco_goals.CanonicalL22VSemantic
import denote.yoco_goals.CanonicalL22Attention

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private theorem cL22V_init_singleton_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid) :
    initSM tid = initPM tid := by
  have h := hInit g hg
  unfold InitGoalHolds at h
  have hv := h.2.2
  rw [reconstructForGoal_of_not_replicated g pm_goal_1.numRanks _ hrep,
    htp, hts, hgd] at hv
  simpa only [List.map, reconstructWithDim] using hv

private theorem cL22V_sm_weight_final (initSM : Store) (tid : Tid)
    (hnot : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
    initSM tid (by native_decide) hnot

private theorem cL22V_pm_weight_final (initPM : Store) (tid : Tid)
    (hnot : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnot

/-- The canonical RMS weight 5596 has the same faithful graph value on SM and PM. -/
theorem canonical_l22_v_rms_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5596 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5596 := by
  have hInitEq := cL22V_init_singleton_eq initSM initPM hInit initGoal_5596
    (by native_decide) 5596 rfl rfl rfl rfl
  have hSM := cL22V_sm_weight_final initSM 5596 (by native_decide)
  have hPM := cL22V_pm_weight_final initPM 5596 (by native_decide)
  rw [hSM, hPM, hInitEq]

/-- The canonical V projection weight 5600 has the same faithful graph value on SM and PM. -/
theorem canonical_l22_v_projection_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5600 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5600 := by
  have hInitEq := cL22V_init_singleton_eq initSM initPM hInit initGoal_5600
    (by native_decide) 5600 rfl rfl rfl rfl
  have hSM := cL22V_sm_weight_final initSM 5600 (by native_decide)
  have hPM := cL22V_pm_weight_final initPM 5600 (by native_decide)
  rw [hSM, hPM, hInitEq]

/-- The faithful PM graph value of the canonical V projection weight has its declared shape. -/
theorem canonical_l22_v_projection_weight_shape (initPM : Store)
    (hPMShapes : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5600).shape = [4, 64, 1024] := by
  have hFinal := cL22V_pm_weight_final initPM 5600 (by native_decide)
  rw [hFinal]
  exact hPMShapes 5600 [4, 64, 1024] (by native_decide)

/-- Rank-0's canonical PM V graph value, isolated from the four-way K/V reduction. -/
theorem canonical_l22_v_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11472 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5600) := by
  have hKV := canonical_l22_kv_pm_reduce initPM
  exact hKV.2.2.1

/-- Rank-1's canonical PM V graph value, isolated from the four-way K/V reduction. -/
theorem canonical_l22_v_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11473 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5600) := by
  have hKV := canonical_l22_kv_pm_reduce initPM
  exact hKV.2.2.2

/-- Close the canonical L22 V graph relation `6203 ↔ 11472/11473` from the
sole preceding attention boundary. -/
theorem canonical_l22_v_relation_from_attention_output
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6203)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11472)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11473)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 4, 64] [2048, 4, 64] := by
  have hCache := canonical_kv_cache_boundary_from_attention_output
    initSM initPM hSM hPM hInit hAttention
  have hRmsW := canonical_l22_v_rms_weight_eq initSM initPM hInit
  have hVW := canonical_l22_v_projection_weight_eq initSM initPM hInit
  have hVShape := canonical_l22_v_projection_weight_shape initPM hPM
  have hSemantic := canonical_l22_v_semantic hCache hRmsW hVW hVShape
  rw [canonical_l22_v_sm_reduce initSM]
  rw [canonical_l22_v_pm0_reduce initPM]
  rw [canonical_l22_v_pm1_reduce initPM]
  exact hSemantic

#print axioms canonical_l22_v_relation_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
