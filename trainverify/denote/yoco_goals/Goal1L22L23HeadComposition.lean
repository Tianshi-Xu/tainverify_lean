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
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11454)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11455)
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

/-- The canonical Goal-1 suffix is closed from the L21 boundary: Q/K/V, the
real sharded-K/V attention nodes, their 3-D to 2-D reshape, the L22 residual
bypass, all of L23, and the CE loss head are composed internally. -/
theorem canonical_goal_1_from_layer21
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hPMValues : InputValueClassesHold Generated.pmInputValueClasses initPM)
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2)
    (hLayer21 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11444)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hlabels : ∀ l < 4096, scalarToNat (valAt (initPM 4931) l) < 154880) :
    InitGoalHolds pm_goal_1.numRanks Generated.goal_1
      (denoteGraphDistributedFaithful sm_goal_1 initSM)
      (denoteGraphDistributedFaithful pm_goal_1 initPM) := by
  have hQKV := canonical_l22_qkv_from_layer21_output initSM initPM
    hSM hPM hInit hLayer21
  have hAttention := canonical_l22_attention_from_qkv initSM initPM hInit
    hPMValues hPacked hQKV.1 hQKV.2.1 hQKV.2.2
  have hResidual := canonical_l22_residual_from_layer21_output initSM initPM hLayer21
  exact canonical_goal_1_from_l22_boundaries initSM initPM hSM hPM hInit hPacked
    hResidual hAttention hlabels

end
end TrainVerify.Denote.GeneratedPatterns
