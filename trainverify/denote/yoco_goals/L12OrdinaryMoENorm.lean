/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L12OrdinaryMoEGraphReductions
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
theorem l12_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8508)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16102)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16110)
      [4096, 1024] [2048, 1024] := by
    rw [l12OMon_red_sm8508 initSM, l12OMon_red_pm16102 initPM, l12OMon_red_pm16110 initPM]
    exact hAttention
  have hw := l12OMon_weight_bridge initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [l12OMon_red_sm5622 initSM, l12OMon_red_pm9818 initPM,
      l12OMon_red_pm9819 initPM, hRef.value, hw,
      ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
        (by omega) (by omega) hRef.shard0_shape hRef.shard1_shape]
  · rw [l12OMon_red_sm5622 initSM]
    exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024
      (by rw [l12OMon_red_sm8508 initSM]; exact hRef.full_shape)
  · rw [l12OMon_red_pm9818 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l12OMon_red_pm16102 initPM]; exact hRef.shard0_shape)
  · rw [l12OMon_red_pm9819 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l12OMon_red_pm16110 initPM]; exact hRef.shard1_shape)

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l12_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8523)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13932)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13933)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l12_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l12OMon_red_sm8523 initSM, l12OMon_red_pm13932 initPM, l12OMon_red_pm13933 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l12_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16114)
      [4096, 1024] [2048, 1024] := by
  rw [l12OMon_red_sm8512 initSM, l12OMon_red_pm16106 initPM, l12OMon_red_pm16114 initPM]
  exact hAttention

#print axioms l12_ordinary_moe_norm_from_attention_output
#print axioms l12_ordinary_moe_activation_from_attention_output
#print axioms l12_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
