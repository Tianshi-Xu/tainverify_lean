/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L4OrdinaryMoEGraphReductions
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
theorem l4_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5177)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8484)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8485)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5179)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8488)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8489)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15582)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15590)
      [4096, 1024] [2048, 1024] := by
    rw [l4OMon_red_sm7973 initSM, l4OMon_red_pm15582 initPM, l4OMon_red_pm15590 initPM]
    exact hAttention
  have hw := l4OMon_weight_bridge initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [l4OMon_red_sm5179 initSM, l4OMon_red_pm8488 initPM,
      l4OMon_red_pm8489 initPM, hRef.value, hw,
      ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
        (by omega) (by omega) hRef.shard0_shape hRef.shard1_shape]
  · rw [l4OMon_red_sm5179 initSM]
    exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024
      (by rw [l4OMon_red_sm7973 initSM]; exact hRef.full_shape)
  · rw [l4OMon_red_pm8488 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l4OMon_red_pm15582 initPM]; exact hRef.shard0_shape)
  · rw [l4OMon_red_pm8489 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l4OMon_red_pm15590 initPM]; exact hRef.shard1_shape)

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l4_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5177)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8484)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8485)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7988)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12914)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12915)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l4_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l4OMon_red_sm7988 initSM, l4OMon_red_pm12914 initPM, l4OMon_red_pm12915 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l4_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5177)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8484)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8485)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15586)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15594)
      [4096, 1024] [2048, 1024] := by
  rw [l4OMon_red_sm7977 initSM, l4OMon_red_pm15586 initPM, l4OMon_red_pm15594 initPM]
  exact hAttention

#print axioms l4_ordinary_moe_norm_from_attention_output
#print axioms l4_ordinary_moe_activation_from_attention_output
#print axioms l4_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
