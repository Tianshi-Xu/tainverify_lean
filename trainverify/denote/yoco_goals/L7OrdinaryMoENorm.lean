/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L7OrdinaryMoEGraphReductions
import denote.yoco_goals.CanonicalKVCacheOrdinaryOps
import denote.Gather2Rel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 500000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section


/-- Ordinary dim-0 RMSNorm transport, stated directly as `Gather2Rel`. -/
theorem l7_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5342)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8976)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8977)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5344)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8980)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8981)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8129)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15678)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15686)
      [4096, 1024] [2048, 1024] := by
    rw [l7OMon_red_sm8129 initSM, l7OMon_red_pm15678 initPM, l7OMon_red_pm15686 initPM]
    exact hAttention
  have hw := l7OMon_weight_bridge initSM initPM hInit
  have hFullShape : (denoteGraphDistributedFaithful sm_goal_1 initSM 8129).shape =
      [4096, 1024] := hRef.full_shape
  have hShard0Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15678).shape =
      [2048, 1024] := hRef.shard0_shape
  have hShard1Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15686).shape =
      [2048, 1024] := hRef.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · calc
      denoteGraphDistributedFaithful sm_goal_1 initSM 5344 =
          fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8129)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5343) :=
        l7OMon_red_sm5344 initSM
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15678,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15686])
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5343) := by
        rw [hRef.value]
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15678,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15686])
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5343) := by
        rw [hw]
      _ = allGatherPrimDimN 0 2 0
            [fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15678)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 5343),
             fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15686)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 5343)] :=
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
          (by omega) (by omega) hShard0Shape hShard1Shape
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_1 initPM 8980,
             denoteGraphDistributedFaithful pm_goal_1 initPM 8981] := by
        rw [l7OMon_red_pm8980 initPM, l7OMon_red_pm8981 initPM]
  · calc
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5344).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8129)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5343)).shape :=
        congrArg Tensor.shape (l7OMon_red_sm5344 initSM)
      _ = [4096, 1024] := ordinary_fw_rms_norm_shape2 _ _ 4096 1024 hFullShape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8980).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15678)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5343)).shape :=
        congrArg Tensor.shape (l7OMon_red_pm8980 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard0Shape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8981).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15686)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5343)).shape :=
        congrArg Tensor.shape (l7OMon_red_pm8981 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard1Shape

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l7_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5342)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8976)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8977)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8144)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13292)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13293)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l7_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l7OMon_red_sm8144 initSM, l7OMon_red_pm13292 initPM, l7OMon_red_pm13293 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l7_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5342)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8976)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8977)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8133)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15682)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15690)
      [4096, 1024] [2048, 1024] := by
  rw [l7OMon_red_sm8133 initSM, l7OMon_red_pm15682 initPM, l7OMon_red_pm15690 initPM]
  exact hAttention

#print axioms l7_ordinary_moe_norm_from_attention_output
#print axioms l7_ordinary_moe_activation_from_attention_output
#print axioms l7_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
