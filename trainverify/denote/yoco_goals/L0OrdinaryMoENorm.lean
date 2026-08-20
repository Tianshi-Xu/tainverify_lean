/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L0OrdinaryMoEGraphReductions
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
theorem l0_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4957)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7829)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4959)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7832)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7833)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7765)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15454)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15462)
      [4096, 1024] [2048, 1024] := by
    rw [l0OMon_red_sm7765 initSM, l0OMon_red_pm15454 initPM, l0OMon_red_pm15462 initPM]
    exact hAttention
  have hw := l0OMon_weight_bridge initSM initPM hInit
  have hFullShape : (denoteGraphDistributedFaithful sm_goal_1 initSM 7765).shape =
      [4096, 1024] := hRef.full_shape
  have hShard0Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15454).shape =
      [2048, 1024] := hRef.shard0_shape
  have hShard1Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15462).shape =
      [2048, 1024] := hRef.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · calc
      denoteGraphDistributedFaithful sm_goal_1 initSM 4959 =
          fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 7765)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 4958) :=
        l0OMon_red_sm4959 initSM
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15454,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15462])
            (denoteGraphDistributedFaithful sm_goal_1 initSM 4958) := by
        rw [hRef.value]
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15454,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15462])
            (denoteGraphDistributedFaithful pm_goal_1 initPM 4958) := by
        rw [hw]
      _ = allGatherPrimDimN 0 2 0
            [fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15454)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 4958),
             fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15462)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 4958)] :=
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
          (by omega) (by omega) hShard0Shape hShard1Shape
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_1 initPM 7832,
             denoteGraphDistributedFaithful pm_goal_1 initPM 7833] := by
        rw [l0OMon_red_pm7832 initPM, l0OMon_red_pm7833 initPM]
  · calc
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4959).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 7765)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 4958)).shape :=
        congrArg Tensor.shape (l0OMon_red_sm4959 initSM)
      _ = [4096, 1024] := ordinary_fw_rms_norm_shape2 _ _ 4096 1024 hFullShape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7832).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15454)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 4958)).shape :=
        congrArg Tensor.shape (l0OMon_red_pm7832 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard0Shape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7833).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15462)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 4958)).shape :=
        congrArg Tensor.shape (l0OMon_red_pm7833 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard1Shape

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l0_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4957)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7829)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7780)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12410)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12411)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l0_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l0OMon_red_sm7780 initSM, l0OMon_red_pm12410 initPM, l0OMon_red_pm12411 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l0_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4957)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7829)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7769)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15458)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15466)
      [4096, 1024] [2048, 1024] := by
  rw [l0OMon_red_sm7769 initSM, l0OMon_red_pm15458 initPM, l0OMon_red_pm15466 initPM]
  exact hAttention

#print axioms l0_ordinary_moe_norm_from_attention_output
#print axioms l0_ordinary_moe_activation_from_attention_output
#print axioms l0_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
