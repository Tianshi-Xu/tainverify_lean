/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.CanonicalKVCacheGraphReductions
import denote.yoco_goals.CanonicalKVCacheOrdinaryOps
import denote.Gather2Rel

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


/-- Ordinary dim-0 RMSNorm transport, stated directly as `Gather2Rel`. -/
theorem canonical_kv_cache_ordinary_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5564)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9637)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8337)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15806)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15814)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCon_red_sm8337 initSM, cKVCon_red_pm15806 initPM, cKVCon_red_pm15814 initPM]
    exact hAttention
  have hw := cKVCon_weight_bridge initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [cKVCon_red_sm5564 initSM, cKVCon_red_pm9636 initPM,
      cKVCon_red_pm9637 initPM, hRef.value, hw,
      ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
        (by omega) (by omega) hRef.shard0_shape hRef.shard1_shape]
  · rw [cKVCon_red_sm5564 initSM]
    exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024
      (by rw [cKVCon_red_sm8337 initSM]; exact hRef.full_shape)
  · rw [cKVCon_red_pm9636 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [cKVCon_red_pm15806 initPM]; exact hRef.shard0_shape)
  · rw [cKVCon_red_pm9637 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [cKVCon_red_pm15814 initPM]; exact hRef.shard1_shape)

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem canonical_kv_cache_ordinary_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8352)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13796)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13797)
      [4096, 1024] [2048, 1024] := by
  have hNorm := canonical_kv_cache_ordinary_norm_from_attention_output initSM initPM hInit hAttention
  rw [cKVCon_red_sm8352 initSM, cKVCon_red_pm13796 initPM, cKVCon_red_pm13797 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem canonical_kv_cache_ordinary_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8341)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15810)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15818)
      [4096, 1024] [2048, 1024] := by
  rw [cKVCon_red_sm8341 initSM, cKVCon_red_pm15810 initPM, cKVCon_red_pm15818 initPM]
  exact hAttention

#print axioms canonical_kv_cache_ordinary_norm_from_attention_output
#print axioms canonical_kv_cache_ordinary_activation_from_attention_output
#print axioms canonical_kv_cache_ordinary_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
