/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L5OrdinaryMoEGraphReductions
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
theorem l5_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8649)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8652)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8653)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8025)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15614)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15622)
      [4096, 1024] [2048, 1024] := by
    rw [l5OMon_red_sm8025 initSM, l5OMon_red_pm15614 initPM, l5OMon_red_pm15622 initPM]
    exact hAttention
  have hw := l5OMon_weight_bridge initSM initPM hInit
  have hFullShape : (denoteGraphDistributedFaithful sm_goal_1 initSM 8025).shape =
      [4096, 1024] := hRef.full_shape
  have hShard0Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15614).shape =
      [2048, 1024] := hRef.shard0_shape
  have hShard1Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15622).shape =
      [2048, 1024] := hRef.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · calc
      denoteGraphDistributedFaithful sm_goal_1 initSM 5234 =
          fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8025)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5233) :=
        l5OMon_red_sm5234 initSM
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15614,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15622])
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5233) := by
        rw [hRef.value]
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15614,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15622])
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5233) := by
        rw [hw]
      _ = allGatherPrimDimN 0 2 0
            [fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15614)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 5233),
             fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15622)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 5233)] :=
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
          (by omega) (by omega) hShard0Shape hShard1Shape
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_1 initPM 8652,
             denoteGraphDistributedFaithful pm_goal_1 initPM 8653] := by
        rw [l5OMon_red_pm8652 initPM, l5OMon_red_pm8653 initPM]
  · calc
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5234).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8025)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5233)).shape :=
        congrArg Tensor.shape (l5OMon_red_sm5234 initSM)
      _ = [4096, 1024] := ordinary_fw_rms_norm_shape2 _ _ 4096 1024 hFullShape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8652).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15614)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5233)).shape :=
        congrArg Tensor.shape (l5OMon_red_pm8652 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard0Shape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8653).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15622)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5233)).shape :=
        congrArg Tensor.shape (l5OMon_red_pm8653 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard1Shape

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l5_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8649)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8040)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13040)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13041)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l5_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l5OMon_red_sm8040 initSM, l5OMon_red_pm13040 initPM, l5OMon_red_pm13041 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l5_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8649)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8029)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15618)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15626)
      [4096, 1024] [2048, 1024] := by
  rw [l5OMon_red_sm8029 initSM, l5OMon_red_pm15618 initPM, l5OMon_red_pm15626 initPM]
  exact hAttention

#print axioms l5_ordinary_moe_norm_from_attention_output
#print axioms l5_ordinary_moe_activation_from_attention_output
#print axioms l5_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
