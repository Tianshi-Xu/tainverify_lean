/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L10OrdinaryMoEGraphReductions
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
theorem l10_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5507)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9468)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9469)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5509)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9472)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9473)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8285)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15774)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15782)
      [4096, 1024] [2048, 1024] := by
    rw [l10OMon_red_sm8285 initSM, l10OMon_red_pm15774 initPM, l10OMon_red_pm15782 initPM]
    exact hAttention
  have hw := l10OMon_weight_bridge initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [l10OMon_red_sm5509 initSM, l10OMon_red_pm9472 initPM,
      l10OMon_red_pm9473 initPM, hRef.value, hw,
      ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
        (by omega) (by omega) hRef.shard0_shape hRef.shard1_shape]
  · rw [l10OMon_red_sm5509 initSM]
    exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024
      (by rw [l10OMon_red_sm8285 initSM]; exact hRef.full_shape)
  · rw [l10OMon_red_pm9472 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l10OMon_red_pm15774 initPM]; exact hRef.shard0_shape)
  · rw [l10OMon_red_pm9473 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l10OMon_red_pm15782 initPM]; exact hRef.shard1_shape)

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l10_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5507)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9468)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9469)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8300)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13670)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13671)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l10_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l10OMon_red_sm8300 initSM, l10OMon_red_pm13670 initPM, l10OMon_red_pm13671 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l10_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5507)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9468)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9469)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8289)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15778)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15786)
      [4096, 1024] [2048, 1024] := by
  rw [l10OMon_red_sm8289 initSM, l10OMon_red_pm15778 initPM, l10OMon_red_pm15786 initPM]
  exact hAttention

#print axioms l10_ordinary_moe_norm_from_attention_output
#print axioms l10_ordinary_moe_activation_from_attention_output
#print axioms l10_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
