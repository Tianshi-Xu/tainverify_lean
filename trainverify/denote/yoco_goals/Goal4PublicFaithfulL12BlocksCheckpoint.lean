/- Goal 4 faithful checkpoint through all three layer-12 blocks. -/
import denote.ZigzagCollective
import denote.yoco_goals.Goal4PublicFaithfulL12OutputCheckpoint
import denote.yoco_goals.L12Block2ZigzagMoERouter
import denote.yoco_goals.Goal1L12Block3MoERouter

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section

structure Goal4L12BlocksCheckpoint (initSM initPM : Store) : Prop where
  base : Goal4L12OutputCheckpoint initSM initPM
  output12b3 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5761)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 10212)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 10213)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024]
  l13 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5682)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9987)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5710) [4096, 64] [2048, 64]
  l14 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5736)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10141)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5764) [4096, 64] [2048, 64]

theorem goal4_l12_blocks_checkpoint_from_l12
    (initSM initPM : Store)
    (hSM1 : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hCore : Goal1AncestryInputContract initSM initPM)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (mid : Goal4L12OutputCheckpoint initSM initPM) :
    Goal4L12BlocksCheckpoint initSM initPM := by
  have hCache := mid.base.cache
  have hA12b2 := canonical_l12b2_attention_residual_from_incoming_and_cache
    initSM initPM hPM1 hInit1 mid.output12 hCache hCore
  have hN12b2 := l12b2_zigzag_moe_norm_from_attention_output initSM initPM hInit1 hA12b2
  have hAll12b2 := l12b2_zigzag_moe_router_all_from_norm_input initSM initPM hPM1 hInit1 hN12b2
  have hO12b2 := l12b2_zigzag_moe_output_from_attention_output initSM initPM hSM1 hPM1 hInit1 hA12b2
  have hA12b3 := goal1_l12_block3_attention_residual_from_stream_cache
    initSM initPM hPM1 hInit1 hCore hO12b2 hCache
  have hN12b3 := goal1_l12_block3_moe_norm_from_attention_output initSM initPM hInit1 hA12b3
  have hAll12b3 := goal1_l12_block3_moe_router_all_from_norm_input initSM initPM hPM1 hInit1 hN12b3
  have hO12b3 := goal1_l12_block3_moe_output_from_attention_output initSM initPM hSM1 hPM1 hInit1 hA12b3
  have hScore12b2 := goal1_gate_scores_of_logits hAll12b2.2.2 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 558 0 5679 5680 5681 5682 4096 (by native_decide) (by native_decide) (by decide) (by decide) hAll12b2.2.2.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1239 0 9980 9982 9984 9986 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll12b2.2.2.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1240 1 9981 9983 9985 9987 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll12b2.2.2.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
  have hScore12b3 := goal1_gate_scores_of_logits hAll12b3.2.2 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 593 0 5733 5734 5735 5736 4096 (by native_decide) (by native_decide) (by decide) (by decide) hAll12b3.2.2.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1315 0 10134 10136 10138 10140 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll12b3.2.2.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1316 1 10135 10137 10139 10141 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll12b3.2.2.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
  exact {
    base := mid
    output12b3 := hO12b3
    l13 := zigzag_transport hScore12b2
      (goal4_late_sm_to_goal1 initSM 5682 (by decide))
      (goal4_late_pm_to_goal1 initPM 9986 (by decide))
      (goal4_late_pm_to_goal1 initPM 9987 (by decide))
      (goal4_canonical_cu_alias initPM hCore.2.1 5710 (by decide))
    l14 := zigzag_transport hScore12b3
      (goal4_late_sm_to_goal1 initSM 5736 (by decide))
      (goal4_late_pm_to_goal1 initPM 10140 (by decide))
      (goal4_late_pm_to_goal1 initPM 10141 (by decide))
      (goal4_canonical_cu_alias initPM hCore.2.1 5764 (by decide))
  }

theorem goal4_l12_blocks_checkpoint_of_external
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_4InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_4InitEnv)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM) :
    Goal4L12BlocksCheckpoint initSM initPM := by
  have hSM1 := goal4_goal1_sm_shapes initSM initPM hInit
  have hPM1 := goal4_goal1_pm_shapes initSM initPM hInit
  have hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM := hInit
  have h6252 : initPM 6252 = initPM 6250 :=
    hContract.2.1.eq_of_mem (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hPacked6252 : PackedCuSeqlensWF (initPM 6252) 4096 2 := by
    rw [h6252]
    exact hContract.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hCore : Goal1AncestryInputContract initSM initPM :=
    ⟨hContract.1, hContract.2.1, hPacked6252⟩
  have hCuLeaf : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6252 (by native_decide) (by native_decide)
  have hDec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [hCuLeaf]
    exact hPacked6252.decoded_single
  have mid := goal4_l12_output_checkpoint_of_external initSM initPM hSM hPM hInit hContract
  exact goal4_l12_blocks_checkpoint_from_l12 initSM initPM hSM1 hPM1 hInit1 hCore hDec mid

end
end TrainVerify.Denote.GeneratedPatterns
