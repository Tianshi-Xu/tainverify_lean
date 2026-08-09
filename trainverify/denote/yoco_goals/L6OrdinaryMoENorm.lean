/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L6OrdinaryMoEGraphReductions
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
theorem l6_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5287)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8813)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5289)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8816)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8817)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8077)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15646)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15654)
      [4096, 1024] [2048, 1024] := by
    rw [l6OMon_red_sm8077 initSM, l6OMon_red_pm15646 initPM, l6OMon_red_pm15654 initPM]
    exact hAttention
  have hw := l6OMon_weight_bridge initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [l6OMon_red_sm5289 initSM, l6OMon_red_pm8816 initPM,
      l6OMon_red_pm8817 initPM, hRef.value, hw,
      ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
        (by omega) (by omega) hRef.shard0_shape hRef.shard1_shape]
  · rw [l6OMon_red_sm5289 initSM]
    exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024
      (by rw [l6OMon_red_sm8077 initSM]; exact hRef.full_shape)
  · rw [l6OMon_red_pm8816 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l6OMon_red_pm15646 initPM]; exact hRef.shard0_shape)
  · rw [l6OMon_red_pm8817 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l6OMon_red_pm15654 initPM]; exact hRef.shard1_shape)

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l6_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5287)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8813)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8092)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13166)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13167)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l6_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l6OMon_red_sm8092 initSM, l6OMon_red_pm13166 initPM, l6OMon_red_pm13167 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l6_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5287)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8813)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8081)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15650)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15658)
      [4096, 1024] [2048, 1024] := by
  rw [l6OMon_red_sm8081 initSM, l6OMon_red_pm15650 initPM, l6OMon_red_pm15658 initPM]
  exact hAttention

#print axioms l6_ordinary_moe_norm_from_attention_output
#print axioms l6_ordinary_moe_activation_from_attention_output
#print axioms l6_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
