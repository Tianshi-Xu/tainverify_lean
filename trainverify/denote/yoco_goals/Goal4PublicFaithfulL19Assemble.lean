/- Goal 4 faithful layer-19 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL19Score
import denote.ZigzagCollective
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective
noncomputable section
theorem goal4_l19_checkpoint_from_l18
    (initSM initPM : Store)
    (hSM1 : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hClasses : InputValueClassesHold pmInputValueClasses initPM)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (mid : Goal4L18Checkpoint initSM initPM) : Goal4L19Checkpoint initSM initPM := by
  have hA19 := goal4_l19_attention_from_l18 initSM initPM hPM1 hInit1 hClasses hDec mid
  have hN19 := goal4_l19_norm_from_attention initSM initPM hInit1 hA19
  have hAll19 := goal4_l19_router_from_norm initSM initPM hPM1 hInit1 hN19
  have hO19 := goal4_l19_output_from_attention initSM initPM hSM1 hPM1 hInit1 hA19
  have hScore19 := goal4_l19_score_from_router initSM initPM hDec hAll19
  refine { base := mid, output19 := hO19, l21 := ?_ }
  exact zigzag_transport hScore19
      (goal4_late_sm_to_goal1 initSM 6114 (by decide))
      (goal4_late_pm_to_goal1 initPM 11218 (by decide))
      (goal4_late_pm_to_goal1 initPM 11219 (by decide))
      (goal4_canonical_cu_alias initPM hClasses 6142 (by decide))

theorem goal4_l19_checkpoint_of_external
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_4InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_4InitEnv)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM) : Goal4L19Checkpoint initSM initPM := by
  have hSM1 := goal4_goal1_sm_shapes initSM initPM hInit
  have hPM1 := goal4_goal1_pm_shapes initSM initPM hInit
  have hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM := hInit
  have h6252 : initPM 6252 = initPM 6250 := hContract.2.1.eq_of_mem
    (c := pmInputValueClasses[1]'(by native_decide)) (by native_decide) (by native_decide) (by native_decide)
  have hPacked6252 : PackedCuSeqlensWF (initPM 6252) 4096 2 := by
    rw [h6252]; exact hContract.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hCuLeaf : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6252 (by native_decide) (by native_decide)
  have hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [hCuLeaf]; exact hPacked6252.decoded_single
  exact goal4_l19_checkpoint_from_l18 initSM initPM hSM1 hPM1 hInit1 hContract.2.1 hDec
    (goal4_l18_checkpoint_of_external initSM initPM hSM hPM hInit hContract)
end
end TrainVerify.Denote.GeneratedPatterns
