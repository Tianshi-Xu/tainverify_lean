/- Goal 1 external-input ancestry through the complete L18 output. -/
import denote.yoco_goals.Goal1ExternalToL17Composition
import denote.yoco_goals.CanonicalL18ShardedKVAttention
import denote.yoco_goals.L18ZigzagMoEComposition

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
contracts through the real L18 output.  The incoming stream, shared cache,
cumulative-sequence alias and decoded metadata are reconstructed internally. -/
theorem goal1_external_to_l18_output
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hContract : Goal1ExternalInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6085)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11136)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11137)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hL17 := goal1_external_to_l17_output
    initSM initPM hSM hPM hInit hContract
  have hCache := goal1_external_to_cache_faithful_composition
    initSM initPM hSM hPM hInit

  have hpm6042 : denoteGraphDistributedFaithful pm_goal_1 initPM 6042 = initPM 6042 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6042 (by native_decide) (by native_decide)
  have hpm6252 : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6252 (by native_decide) (by native_decide)
  have h6042Init : initPM 6042 = initPM 6252 :=
    hContract.2.1.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hCuAlias18 : denoteGraphDistributedFaithful pm_goal_1 initPM 6042 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hpm6042, hpm6252, h6042Init]
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [hpm6252]
    exact hContract.2.2.1.decoded_single

  have hL18Attention := canonical_l18_attention_residual_from_incoming_and_cache
    initSM initPM hPM hInit hL17 hCache hCuAlias18 hDecoded
  exact l18_zigzag_moe_output_from_attention_output
    initSM initPM hSM hPM hInit hL18Attention

#print axioms goal1_external_to_l18_output

end
end TrainVerify.Denote.GeneratedPatterns
