/- Goal 1 external-input ancestry through the final canonical Goal-1 theorem. -/
import denote.yoco_goals.Goal1ExternalToL18Composition
import denote.yoco_goals.CanonicalL19ShardedKVAttention
import denote.yoco_goals.L19ZigzagMoEComposition
import denote.yoco_goals.CanonicalL20ShardedKVAttention
import denote.yoco_goals.CanonicalL21Composition
import denote.yoco_goals.Goal1L22L23HeadComposition

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
contracts to the canonical Goal-1 output.  Every computed stream and shared
cache relation, both layer-local cumulative-sequence aliases, and the decoded
packed metadata are reconstructed internally. -/
theorem goal1_external_to_canonical_goal_1
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hContract : Goal1ExternalInputContract initSM initPM) :
    InitGoalHolds pm_goal_1.numRanks Generated.goal_1
      (denoteGraphDistributedFaithful sm_goal_1 initSM)
      (denoteGraphDistributedFaithful pm_goal_1 initPM) := by
  have hL18 := goal1_external_to_l18_output
    initSM initPM hSM hPM hInit hContract
  have hCache := goal1_external_to_cache_faithful_composition
    initSM initPM hSM hPM hInit

  have hpm6096 : denoteGraphDistributedFaithful pm_goal_1 initPM 6096 = initPM 6096 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6096 (by native_decide) (by native_decide)
  have hpm6150 : denoteGraphDistributedFaithful pm_goal_1 initPM 6150 = initPM 6150 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6150 (by native_decide) (by native_decide)
  have hpm6252 : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6252 (by native_decide) (by native_decide)
  have h6096Init : initPM 6096 = initPM 6252 :=
    hContract.2.1.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have h6150Init : initPM 6150 = initPM 6252 :=
    hContract.2.1.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hCuAlias19 : denoteGraphDistributedFaithful pm_goal_1 initPM 6096 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hpm6096, hpm6252, h6096Init]
  have hCuAlias20 : denoteGraphDistributedFaithful pm_goal_1 initPM 6150 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hpm6150, hpm6252, h6150Init]
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [hpm6252]
    exact hContract.2.2.1.decoded_single

  have hL19Attention := canonical_l19_attention_residual_from_incoming_and_cache
    initSM initPM hPM hInit hL18 hCache hCuAlias19 hDecoded
  have hL19 := l19_zigzag_moe_output_from_attention_output
    initSM initPM hSM hPM hInit hL19Attention
  have hL20 := canonical_l20_output_from_l19_and_cache
    initSM initPM hPM hInit hL19 hCache hCuAlias20 hDecoded
  have hL21 := canonical_l21_output_from_layer20_output
    initSM initPM hSM hPM hInit hL20
  exact canonical_goal_1_from_layer21 initSM initPM hSM hPM hInit
    hContract.2.1 hContract.2.2.1 hL21 hContract.2.2.2

/-- The generated ancestry-closed external Goal-1 statement is inhabited by the
canonical faithful composition above. -/
theorem canonical_goal_1_external : goal_1_stmt_full := by
  unfold goal_1_stmt_full
  unfold CoarseLineageHoldsWithInitDistributedFaithfulWithContract
  intro initSM initPM hSM hPM hInit hContract
  exact goal1_external_to_canonical_goal_1
    initSM initPM hSM hPM hInit hContract

#print axioms goal1_external_to_canonical_goal_1
#print axioms canonical_goal_1_external

end
end TrainVerify.Denote.GeneratedPatterns
