/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L1OrdinaryMoEGraphReductions
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
theorem l1_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7992)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7993)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5014)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7996)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7997)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7817)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15486)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15494)
      [4096, 1024] [2048, 1024] := by
    rw [l1OMon_red_sm7817 initSM, l1OMon_red_pm15486 initPM, l1OMon_red_pm15494 initPM]
    exact hAttention
  have hw := l1OMon_weight_bridge initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [l1OMon_red_sm5014 initSM, l1OMon_red_pm7996 initPM,
      l1OMon_red_pm7997 initPM, hRef.value, hw,
      ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
        (by omega) (by omega) hRef.shard0_shape hRef.shard1_shape]
  · rw [l1OMon_red_sm5014 initSM]
    exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024
      (by rw [l1OMon_red_sm7817 initSM]; exact hRef.full_shape)
  · rw [l1OMon_red_pm7996 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l1OMon_red_pm15486 initPM]; exact hRef.shard0_shape)
  · rw [l1OMon_red_pm7997 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l1OMon_red_pm15494 initPM]; exact hRef.shard1_shape)

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l1_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7992)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7993)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7832)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12536)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12537)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l1_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l1OMon_red_sm7832 initSM, l1OMon_red_pm12536 initPM, l1OMon_red_pm12537 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l1_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7992)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7993)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7821)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15490)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15498)
      [4096, 1024] [2048, 1024] := by
  rw [l1OMon_red_sm7821 initSM, l1OMon_red_pm15490 initPM, l1OMon_red_pm15498 initPM]
  exact hAttention

#print axioms l1_ordinary_moe_norm_from_attention_output
#print axioms l1_ordinary_moe_activation_from_attention_output
#print axioms l1_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
