/- Goal 4 faithful checkpoint through layer 21. -/
import denote.yoco_goals.Goal4PublicFaithfulL20Checkpoint
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
structure Goal4L21Checkpoint (initSM initPM : Store) : Prop where
  base : Goal4L20Checkpoint initSM initPM
  output21 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6193)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11444)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11445)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024]
  l22 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6168)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11373)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 6196) [4096, 64] [2048, 64]
theorem goal4_l21_checkpoint_from_l20 (initSM initPM : Store)
    (hSM1 : StoreShapesHold initSM sm_goal_1InitEnv) (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hClasses : InputValueClassesHold pmInputValueClasses initPM)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (mid : Goal4L20Checkpoint initSM initPM) : Goal4L21Checkpoint initSM initPM := by
  have hInput : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11354) (denoteGraphDistributedFaithful pm_goal_1 initPM 11355)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024] := mid.output20
  have hN21 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6162)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11358) (denoteGraphDistributedFaithful pm_goal_1 initPM 11359)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024] :=
    canonical_l21_norm_from_layer20_output initSM initPM hInit1 hInput
  have hAll21 := canonical_l21_router_all_from_norm_input initSM initPM hPM1 hInit1 hN21
  have hLogits : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6165)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11366) (denoteGraphDistributedFaithful pm_goal_1 initPM 11367)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := hAll21.2.2
  have hO21 := canonical_l21_output_from_layer20_output initSM initPM hSM1 hPM1 hInit1 hInput
  have hScore21 := goal1_gate_scores_of_logits hLogits hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 873 0 6165 6166 6167 6168 4096 (by native_decide) (by native_decide) (by decide) (by decide) hLogits.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1923 0 11366 11368 11370 11372 2048 (by native_decide) (by native_decide) (by decide) (by decide) hLogits.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1924 1 11367 11369 11371 11373 2048 (by native_decide) (by native_decide) (by decide) (by decide) hLogits.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
  refine { base := mid, output21 := hO21, l22 := ?_ }
  exact zigzag_transport hScore21
      (goal4_late_sm_to_goal1 initSM 6168 (by decide))
      (goal4_late_pm_to_goal1 initPM 11372 (by decide))
      (goal4_late_pm_to_goal1 initPM 11373 (by decide))
      (goal4_canonical_cu_alias initPM hClasses 6196 (by decide))
theorem goal4_l21_checkpoint_of_external (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_4InitEnv) (hPM : StoreShapesHold initPM pm_goal_4InitEnv)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM) : Goal4L21Checkpoint initSM initPM := by
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
  exact goal4_l21_checkpoint_from_l20 initSM initPM hSM1 hPM1 hInit1 hContract.2.1 hDec
    (goal4_l20_checkpoint_of_external initSM initPM hSM hPM hInit hContract)
end
end TrainVerify.Denote.GeneratedPatterns
