/- Canonical Goal 1, layer 13: graph alignment of the K projection. -/
import denote.yoco_goals.CanonicalL13KVGraph
import denote.yoco_goals.CanonicalL13KVSemantic

set_option linter.style.nativeDecide false
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section

private theorem cL13K_init_singleton_eq (initSM initPM : Store)
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

private theorem cL13K_sm_weight_value (initSM : Store) (tid : Tid)
    (hnw : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
    initSM tid (by native_decide) hnw

private theorem cL13K_pm_weight_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private theorem cL13K_rms_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5596 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5596 := by
  have hi := cL13K_init_singleton_eq initSM initPM hInit initGoal_5596
    (by native_decide) 5596 rfl rfl rfl rfl
  have hs := cL13K_sm_weight_value initSM 5596 (by native_decide)
  have hp := cL13K_pm_weight_value initPM 5596 (by native_decide)
  rw [hs, hp, hi]

private theorem cL13K_proj_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5598 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5598 := by
  have hi := cL13K_init_singleton_eq initSM initPM hInit initGoal_5598
    (by native_decide) 5598 rfl rfl rfl rfl
  have hs := cL13K_sm_weight_value initSM 5598 (by native_decide)
  have hp := cL13K_pm_weight_value initPM 5598 (by native_decide)
  rw [hs, hp, hi]

private theorem cL13K_proj_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5598).shape = [4, 64, 1024] := by
  have hp := cL13K_pm_weight_value initPM 5598 (by native_decide)
  rw [hp]
  exact hPM 5598 [4, 64, 1024] (by native_decide)

/-- The complete ordinary canonical L13 K graph relation `5770 ↔ 10234/10235`.
All projection-weight facts are derived from the generated init contracts. -/
theorem canonical_l13_k_ordinary_relation
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5770)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10235)
      [4096, 4, 64] [2048, 4, 64] := by
  have hRmsW := cL13K_rms_weight_eq initSM initPM hInit
  have hKW := cL13K_proj_weight_eq initSM initPM hInit
  have hKShape := cL13K_proj_weight_shape initPM hPM
  have hSemantic := canonical_l13_k_ordinary_semantic hCache hRmsW hKW hKShape
  rw [canonical_l13_k_sm_reduce initSM]
  rw [canonical_l13_k_pm0_reduce initPM]
  rw [canonical_l13_k_pm1_reduce initPM]
  exact hSemantic

#print axioms canonical_l13_k_ordinary_relation

end
end TrainVerify.Denote.GeneratedPatterns
