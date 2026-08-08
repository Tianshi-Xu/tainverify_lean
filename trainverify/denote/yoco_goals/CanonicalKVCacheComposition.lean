/- Canonical Goal 1 cache-source composition from the preceding attention output. -/
import denote.yoco_goals.CanonicalKVCacheNormRouter
import denote.yoco_goals.CanonicalKVCacheExpertDown
import denote.yoco_goals.CanonicalKVCacheDown
import denote.yoco_goals.CanonicalKVCacheRouter

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

/-- Canonical cache-source composition through the faithful `5595 ↔ 9722/9723`
boundary.  Norm, expert activation, scalar gate, dense down, residual bypass,
expert output, and the tail are all derived internally.  The two router tensors
remain explicit internal-boundary premises until the canonical router chain is
closed from the normalized activation. -/
theorem canonical_kv_cache_boundary_from_attention_output_and_router
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hRP : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5568)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9646)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9647)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64])
    (hRM : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5569)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9649)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm := canonical_kv_cache_norm_from_attention_output
    initSM initPM hInit hAttention
  have hActivation := canonical_kv_cache_activation_from_attention_output
    initSM initPM hInit hAttention
  have hResidual := canonical_kv_cache_residual_from_attention_output
    initSM initPM hAttention
  have hGate := canonical_kv_cache_gate_from_attention_output
    initSM initPM hPM hInit hAttention
  have hDown := canonical_kv_cache_down_from_norm_input
    initSM initPM hPM hInit hNorm
  have hExpert := canonical_kv_cache_expert_from_branch_inputs
    initSM initPM hSM hPM hInit hActivation hRP hRM
  exact canonical_kv_cache_boundary_from_branch_inputs
    initSM initPM hResidual hExpert hGate hDown

/-- Complete cache-source layer composition.  The preceding faithful attention
output is the sole computed-lineage boundary; router probabilities and maps are
derived internally from that same input. -/
theorem canonical_kv_cache_boundary_from_attention_output
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
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hRouter := canonical_kv_cache_router_from_attention_output
    initSM initPM hPM hInit hAttention
  exact canonical_kv_cache_boundary_from_attention_output_and_router
    initSM initPM hSM hPM hInit hAttention hRouter.1 hRouter.2

#print axioms canonical_kv_cache_boundary_from_attention_output_and_router
#print axioms canonical_kv_cache_boundary_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
