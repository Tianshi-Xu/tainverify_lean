/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L3OrdinaryMoEGraphReductions
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
theorem l3_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8320)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8321)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5124)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8324)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8325)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7921)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15550)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15558)
      [4096, 1024] [2048, 1024] := by
    rw [l3OMon_red_sm7921 initSM, l3OMon_red_pm15550 initPM, l3OMon_red_pm15558 initPM]
    exact hAttention
  have hw := l3OMon_weight_bridge initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [l3OMon_red_sm5124 initSM, l3OMon_red_pm8324 initPM,
      l3OMon_red_pm8325 initPM, hRef.value, hw,
      ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
        (by omega) (by omega) hRef.shard0_shape hRef.shard1_shape]
  · rw [l3OMon_red_sm5124 initSM]
    exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024
      (by rw [l3OMon_red_sm7921 initSM]; exact hRef.full_shape)
  · rw [l3OMon_red_pm8324 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l3OMon_red_pm15550 initPM]; exact hRef.shard0_shape)
  · rw [l3OMon_red_pm8325 initPM]
    exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024
      (by rw [l3OMon_red_pm15558 initPM]; exact hRef.shard1_shape)

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l3_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8320)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8321)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7936)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12788)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12789)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l3_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l3OMon_red_sm7936 initSM, l3OMon_red_pm12788 initPM, l3OMon_red_pm12789 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l3_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8320)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8321)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7925)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15554)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15562)
      [4096, 1024] [2048, 1024] := by
  rw [l3OMon_red_sm7925 initSM, l3OMon_red_pm15554 initPM, l3OMon_red_pm15562 initPM]
  exact hAttention

#print axioms l3_ordinary_moe_norm_from_attention_output
#print axioms l3_ordinary_moe_activation_from_attention_output
#print axioms l3_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
