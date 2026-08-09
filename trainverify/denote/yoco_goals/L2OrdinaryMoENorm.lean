/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L2OrdinaryMoEGraphReductions
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
theorem l2_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5067)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8156)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8157)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5069)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8161)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7869)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15518)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15526)
      [4096, 1024] [2048, 1024] := by
    rw [l2OMon_red_sm7869 initSM, l2OMon_red_pm15518 initPM, l2OMon_red_pm15526 initPM]
    exact hAttention
  have hw := l2OMon_weight_bridge initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [l2OMon_red_sm5069 initSM, l2OMon_red_pm8160 initPM,
      l2OMon_red_pm8161 initPM, hRef.value, hw,
      ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
        (by omega) (by omega) hRef.shard0_shape hRef.shard1_shape]
  · rw [l2OMon_red_sm5069 initSM]
    exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024
      (by rw [l2OMon_red_sm7869 initSM]; exact hRef.full_shape)
  · rw [l2OMon_red_pm8160 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l2OMon_red_pm15518 initPM]; exact hRef.shard0_shape)
  · rw [l2OMon_red_pm8161 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l2OMon_red_pm15526 initPM]; exact hRef.shard1_shape)

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l2_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5067)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8156)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8157)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12662)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12663)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l2_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l2OMon_red_sm7884 initSM, l2OMon_red_pm12662 initPM, l2OMon_red_pm12663 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l2_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5067)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8156)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8157)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7873)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15522)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15530)
      [4096, 1024] [2048, 1024] := by
  rw [l2OMon_red_sm7873 initSM, l2OMon_red_pm15522 initPM, l2OMon_red_pm15530 initPM]
  exact hAttention

#print axioms l2_ordinary_moe_norm_from_attention_output
#print axioms l2_ordinary_moe_activation_from_attention_output
#print axioms l2_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
