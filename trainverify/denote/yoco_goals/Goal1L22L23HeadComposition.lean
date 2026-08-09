/- Canonical Goal 1: compose the L22 post-shuffle interface through L23 and the loss head. -/
import denote.yoco_goals.Goal1ExternalToCacheComposition
import denote.yoco_goals.CanonicalL22AttentionComposition
import denote.yoco_goals.CanonicalL22KAlignment
import denote.yoco_goals.CanonicalL22VAlignment
import denote.yoco_goals.CanonicalL22Residual
import denote.yoco_goals.CanonicalL23Composition

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-- The exact L22 post-shuffle Q/K/V interface.  The shared cache relation is
not a caller premise: it is reconstructed internally from the external/init
contracts by `goal1_external_to_cache_faithful_composition`. -/
theorem canonical_l22_qkv_from_layer21_output
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hLayer21 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11444)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6201)
        (fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11452)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 6200))
        (fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11453)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 6200))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
        [4096, 16, 64] [2048, 16, 64] ∧
      Gather2Rel
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6202)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11466)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11467)
        [4096, 4, 64] [2048, 4, 64] ∧
      Gather2Rel
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6203)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11472)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11473)
        [4096, 4, 64] [2048, 4, 64] := by
  have hCache := goal1_external_to_cache_faithful_composition initSM initPM hSM hPM hInit
  refine ⟨canonical_l22_q_relation_from_l21 initSM initPM hPM hInit hLayer21,
    canonical_l22_k_ordinary_relation initSM initPM hPM hInit hCache,
    canonical_l22_v_ordinary_relation initSM initPM hPM hInit hCache⟩

/-- Green suffix from the sole unresolved L22 attention-output relation through
all of L23, unshuffle/RMSNorm, and the faithful Goal-1 CE loss head.  The L22
residual bypass is derived from the L21 output rather than assumed. -/
theorem canonical_goal_1_from_layer21_and_l22_attention
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2)
    (hLayer21 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11444)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hlabels : ∀ l < 4096, scalarToNat (valAt (initPM 4931) l) < 154880) :
    InitGoalHolds pm_goal_1.numRanks Generated.goal_1
      (denoteGraphDistributedFaithful sm_goal_1 initSM)
      (denoteGraphDistributedFaithful pm_goal_1 initPM) := by
  have hResidual := canonical_l22_residual_from_layer21_output initSM initPM hLayer21
  exact canonical_goal_1_from_l22_boundaries initSM initPM hSM hPM hInit hPacked
    hResidual hAttention hlabels

end
end TrainVerify.Denote.GeneratedPatterns
