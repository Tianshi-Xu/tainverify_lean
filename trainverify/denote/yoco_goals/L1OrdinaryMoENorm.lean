/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L1OrdinaryMoEGraphReductions
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
  have hFullShape : (denoteGraphDistributedFaithful sm_goal_1 initSM 7817).shape =
      [4096, 1024] := hRef.full_shape
  have hShard0Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15486).shape =
      [2048, 1024] := hRef.shard0_shape
  have hShard1Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15494).shape =
      [2048, 1024] := hRef.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · calc
      denoteGraphDistributedFaithful sm_goal_1 initSM 5014 =
          fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 7817)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5013) :=
        l1OMon_red_sm5014 initSM
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15486,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15494])
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5013) := by
        rw [hRef.value]
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15486,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15494])
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5013) := by
        rw [hw]
      _ = allGatherPrimDimN 0 2 0
            [fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15486)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 5013),
             fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15494)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 5013)] :=
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
          (by omega) (by omega) hShard0Shape hShard1Shape
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_1 initPM 7996,
             denoteGraphDistributedFaithful pm_goal_1 initPM 7997] := by
        rw [l1OMon_red_pm7996 initPM, l1OMon_red_pm7997 initPM]
  · calc
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5014).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 7817)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5013)).shape :=
        congrArg Tensor.shape (l1OMon_red_sm5014 initSM)
      _ = [4096, 1024] := ordinary_fw_rms_norm_shape2 _ _ 4096 1024 hFullShape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7996).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15486)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5013)).shape :=
        congrArg Tensor.shape (l1OMon_red_pm7996 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard0Shape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7997).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15494)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5013)).shape :=
        congrArg Tensor.shape (l1OMon_red_pm7997 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard1Shape

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
