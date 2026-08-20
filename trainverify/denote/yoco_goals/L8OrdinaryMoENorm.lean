/- Canonical Goal 1 cache-source ordinary ancestry: attention output through RMSNorm. -/
import denote.yoco_goals.L8OrdinaryMoEGraphReductions
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
theorem l8_ordinary_moe_norm_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9140)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9141)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5399)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9144)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9145)
      [4096, 1024] [2048, 1024] := by
  have hRef : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8181)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15710)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15718)
      [4096, 1024] [2048, 1024] := by
    rw [l8OMon_red_sm8181 initSM, l8OMon_red_pm15710 initPM, l8OMon_red_pm15718 initPM]
    exact hAttention
  have hw := l8OMon_weight_bridge initSM initPM hInit
  have hFullShape : (denoteGraphDistributedFaithful sm_goal_1 initSM 8181).shape =
      [4096, 1024] := hRef.full_shape
  have hShard0Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15710).shape =
      [2048, 1024] := hRef.shard0_shape
  have hShard1Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 15718).shape =
      [2048, 1024] := hRef.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · calc
      denoteGraphDistributedFaithful sm_goal_1 initSM 5399 =
          fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8181)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5398) :=
        l8OMon_red_sm5399 initSM
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15710,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15718])
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5398) := by
        rw [hRef.value]
      _ = fw_rms_norm
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_1 initPM 15710,
               denoteGraphDistributedFaithful pm_goal_1 initPM 15718])
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5398) := by
        rw [hw]
      _ = allGatherPrimDimN 0 2 0
            [fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15710)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 5398),
             fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15718)
                (denoteGraphDistributedFaithful pm_goal_1 initPM 5398)] :=
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024
          (by omega) (by omega) hShard0Shape hShard1Shape
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_1 initPM 9144,
             denoteGraphDistributedFaithful pm_goal_1 initPM 9145] := by
        rw [l8OMon_red_pm9144 initPM, l8OMon_red_pm9145 initPM]
  · calc
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5399).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8181)
            (denoteGraphDistributedFaithful sm_goal_1 initSM 5398)).shape :=
        congrArg Tensor.shape (l8OMon_red_sm5399 initSM)
      _ = [4096, 1024] := ordinary_fw_rms_norm_shape2 _ _ 4096 1024 hFullShape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9144).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15710)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5398)).shape :=
        congrArg Tensor.shape (l8OMon_red_pm9144 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard0Shape
  · calc
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9145).shape =
          (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15718)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 5398)).shape :=
        congrArg Tensor.shape (l8OMon_red_pm9145 initPM)
      _ = [2048, 1024] := ordinary_fw_rms_norm_shape2 _ _ 2048 1024 hShard1Shape

/-- The real activation input aliases preserve the ordinary dim-0 relation. -/
theorem l8_ordinary_moe_activation_from_attention_output (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9140)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9141)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8196)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13418)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13419)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l8_ordinary_moe_norm_from_attention_output initSM initPM hInit hAttention
  rw [l8OMon_red_sm8196 initSM, l8OMon_red_pm13418 initPM, l8OMon_red_pm13419 initPM]
  exact hNorm


/-- The residual bypass is the second real multiref output and preserves ordinary layout. -/
theorem l8_ordinary_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9140)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9141)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8185)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15714)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15722)
      [4096, 1024] [2048, 1024] := by
  rw [l8OMon_red_sm8185 initSM, l8OMon_red_pm15714 initPM, l8OMon_red_pm15722 initPM]
  exact hAttention

#print axioms l8_ordinary_moe_norm_from_attention_output
#print axioms l8_ordinary_moe_activation_from_attention_output
#print axioms l8_ordinary_moe_residual_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
