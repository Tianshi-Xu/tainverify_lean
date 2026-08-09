/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L9OrdinaryMoEGraphReductions
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
theorem l9_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5452)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9304)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9305)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5454)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9308)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9309)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8233)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15750)
      [4096, 1024] [2048, 1024] := by
    rw [l9OMon_red_sm8233 initSM, l9OMon_red_pm15742 initPM, l9OMon_red_pm15750 initPM]
    exact hAttention
  have hw := l9OMon_weight_bridge initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [l9OMon_red_sm5454 initSM, l9OMon_red_pm9308 initPM,
      l9OMon_red_pm9309 initPM, hRef.value, hw,
      ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
        (by omega) (by omega) hRef.shard0_shape hRef.shard1_shape]
  · rw [l9OMon_red_sm5454 initSM]
    exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024
      (by rw [l9OMon_red_sm8233 initSM]; exact hRef.full_shape)
  · rw [l9OMon_red_pm9308 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l9OMon_red_pm15742 initPM]; exact hRef.shard0_shape)
  · rw [l9OMon_red_pm9309 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l9OMon_red_pm15750 initPM]; exact hRef.shard1_shape)

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l9_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5452)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9304)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9305)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8248)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13544)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13545)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l9_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l9OMon_red_sm8248 initSM, l9OMon_red_pm13544 initPM, l9OMon_red_pm13545 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l9_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5452)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9304)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9305)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8237)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15746)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15754)
      [4096, 1024] [2048, 1024] := by
  rw [l9OMon_red_sm8237 initSM, l9OMon_red_pm15746 initPM, l9OMon_red_pm15754 initPM]
  exact hAttention

#print axioms l9_ordinary_moe_norm_from_attention_output
#print axioms l9_ordinary_moe_activation_from_attention_output
#print axioms l9_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
