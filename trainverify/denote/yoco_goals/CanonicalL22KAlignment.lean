/- Canonical Goal 1, layer 22: graph alignment of the K projection. -/
import denote.yoco_goals.CanonicalL22KSemantic
import denote.yoco_goals.CanonicalL22Attention

set_option linter.style.nativeDecide false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private theorem cL22K_init_singleton_eq (initSM initPM : Store)
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

private theorem cL22K_sm_weight_value (initSM : Store) (tid : Tid)
    (hnw : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
    initSM tid (by native_decide) hnw

private theorem cL22K_pm_weight_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private theorem cL22K_rms_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5596 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5596 := by
  have hi := cL22K_init_singleton_eq initSM initPM hInit initGoal_5596
    (by native_decide) 5596 rfl rfl rfl rfl
  have hs := cL22K_sm_weight_value initSM 5596 (by native_decide)
  have hp := cL22K_pm_weight_value initPM 5596 (by native_decide)
  rw [hs, hp, hi]

private theorem cL22K_proj_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5598 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5598 := by
  have hi := cL22K_init_singleton_eq initSM initPM hInit initGoal_5598
    (by native_decide) 5598 rfl rfl rfl rfl
  have hs := cL22K_sm_weight_value initSM 5598 (by native_decide)
  have hp := cL22K_pm_weight_value initPM 5598 (by native_decide)
  rw [hs, hp, hi]

private theorem cL22K_proj_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5598).shape = [4, 64, 1024] := by
  have hp := cL22K_pm_weight_value initPM 5598 (by native_decide)
  rw [hp]
  exact hPM 5598 [4, 64, 1024] (by native_decide)

/-- The canonical L22 K graph tensors are related from the unique cache boundary.
Weight equality and shape are discharged from the generated init contracts. -/
theorem canonical_l22_k_relation
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hCache : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11466)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11467)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 4, 64] [2048, 4, 64] := by
  have hRmsW := cL22K_rms_weight_eq initSM initPM hInit
  have hKW := cL22K_proj_weight_eq initSM initPM hInit
  have hKShape := cL22K_proj_weight_shape initPM hPM
  have hSemantic := canonical_l22_k_semantic hCache hRmsW hKW hKShape
  have hPM := canonical_l22_kv_pm_reduce initPM
  have hPM0 := hPM.1
  have hPM1 := hPM.2.1
  have hSM := canonical_l22_k_sm_reduce initSM
  rw [hSM, hPM0, hPM1]
  exact hSemantic

/-- The real canonical L22 K segment preserves ordinary rank-order gather. -/
theorem canonical_l22_k_ordinary_relation
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11466)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11467)
      [4096, 4, 64] [2048, 4, 64] := by
  have hRmsW := cL22K_rms_weight_eq initSM initPM hInit
  have hKW := cL22K_proj_weight_eq initSM initPM hInit
  have hKShape := cL22K_proj_weight_shape initPM hPM
  have hSemantic := canonical_l22_k_ordinary_semantic hCache hRmsW hKW hKShape
  have hPM := canonical_l22_kv_pm_reduce initPM
  rw [canonical_l22_k_sm_reduce initSM, hPM.1, hPM.2.1]
  exact hSemantic

#print axioms canonical_l22_k_relation
#print axioms canonical_l22_k_ordinary_relation

end
end TrainVerify.Denote.GeneratedPatterns
