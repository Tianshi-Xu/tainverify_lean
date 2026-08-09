/- Goal 1 external-input ancestry through the complete L17 output. -/
import denote.yoco_goals.Goal1ExternalToL16Composition
import denote.yoco_goals.CanonicalL17ShardedKVAttention
import denote.yoco_goals.L17ZigzagMoEComposition

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

/-- Complete faithful Goal-1 ancestry from the independent external/init
contracts through the real L17 output.  The incoming stream, shared cache,
cumulative-sequence alias and decoded metadata are reconstructed internally. -/
theorem goal1_external_to_l17_output
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hContract : Goal1ExternalInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6031)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10982)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hL16 := goal1_external_to_l16_output
    initSM initPM hSM hPM hInit hContract
  have hCache := goal1_external_to_cache_faithful_composition
    initSM initPM hSM hPM hInit

  have hpm5988 : denoteGraphDistributedFaithful pm_goal_1 initPM 5988 = initPM 5988 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 5988 (by native_decide) (by native_decide)
  have hpm6252 : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6252 (by native_decide) (by native_decide)
  have h5988Init : initPM 5988 = initPM 6252 :=
    hContract.2.1.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hCuAlias17 : denoteGraphDistributedFaithful pm_goal_1 initPM 5988 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hpm5988, hpm6252, h5988Init]
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [hpm6252]
    exact hContract.2.2.1.decoded_single

  have hL17Attention := canonical_l17_attention_residual_from_incoming_and_cache
    initSM initPM hPM hInit hL16 hCache hCuAlias17 hDecoded
  exact l17_zigzag_moe_output_from_attention_output
    initSM initPM hSM hPM hInit hL17Attention

#print axioms goal1_external_to_l17_output

end
end TrainVerify.Denote.GeneratedPatterns
