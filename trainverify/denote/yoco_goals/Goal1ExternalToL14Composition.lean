/- Goal 1 external-input ancestry through the complete L14 output. -/
import denote.yoco_goals.CanonicalL12ShardedKVAttention
import denote.yoco_goals.L12ZigzagMoEComposition
import denote.yoco_goals.CanonicalL12Block2Composition
import denote.yoco_goals.Goal1L12ThirdZigzagBlock
import denote.yoco_goals.CanonicalL13ShardedKVAttention
import denote.yoco_goals.L13ZigzagMoEComposition
import denote.yoco_goals.CanonicalL14ShardedKVAttention
import denote.yoco_goals.L14ZigzagMoEComposition

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
contracts through the real L14 output.  The shared cache, cumulative-sequence
aliases and decoded metadata, and every intermediate stream relation are
reconstructed internally. -/
theorem goal1_external_to_l14_output
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hContract : Goal1AncestryInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5869)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10520)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10521)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hL12Attention := goal1_external_to_l12_attention_residual
    initSM initPM hSM hPM hInit hContract
  have hL12 := l12_zigzag_moe_output_from_attention_output
    initSM initPM hSM hPM hInit hL12Attention
  have hCache := goal1_external_to_cache_faithful_composition
    initSM initPM hSM hPM hInit
  have hL12Block2 := canonical_l12b2_from_incoming_and_cache
    initSM initPM hSM hPM hInit hL12 hCache hContract
  have hL12Block3 := goal1_l12_third_zigzag_block
    initSM initPM hSM hPM hInit hContract hL12Block2 hCache

  have hpm5772 : denoteGraphDistributedFaithful pm_goal_1 initPM 5772 = initPM 5772 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 5772 (by native_decide) (by native_decide)
  have hpm5826 : denoteGraphDistributedFaithful pm_goal_1 initPM 5826 = initPM 5826 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 5826 (by native_decide) (by native_decide)
  have hpm6252 : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6252 (by native_decide) (by native_decide)
  have h5772Init : initPM 5772 = initPM 6252 :=
    hContract.2.1.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have h5826Init : initPM 5826 = initPM 6252 :=
    hContract.2.1.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hCuAlias13 : denoteGraphDistributedFaithful pm_goal_1 initPM 5772 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hpm5772, hpm6252, h5772Init]
  have hCuAlias14 : denoteGraphDistributedFaithful pm_goal_1 initPM 5826 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hpm5826, hpm6252, h5826Init]
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [hpm6252]
    exact hContract.2.2.decoded_single

  have hL13Attention := canonical_l13_attention_residual_from_incoming_and_cache
    initSM initPM hPM hInit hL12Block3 hCache hCuAlias13 hDecoded
  have hL13 := l13_zigzag_moe_output_from_attention_output
    initSM initPM hSM hPM hInit hL13Attention
  have hL14Attention := canonical_l14_attention_residual_from_incoming_and_cache
    initSM initPM hPM hInit hL13 hCache hCuAlias14 hDecoded
  exact l14_zigzag_moe_output_from_attention_output
    initSM initPM hSM hPM hInit hL14Attention

#print axioms goal1_external_to_l14_output

end
end TrainVerify.Denote.GeneratedPatterns
