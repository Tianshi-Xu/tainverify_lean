/- Goal 4 faithful layer-13 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL13Output
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l13_score_from_router
    (initSM initPM : Store)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (hAll13 :
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5788)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10290)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10291)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5789)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10292)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10293)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5787)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10288)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10289)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5790)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10294)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10295)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact goal1_gate_scores_of_logits hAll13.2.2 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 628 0 5787 5788 5789 5790 4096 (by native_decide) (by native_decide) (by decide) (by decide) hAll13.2.2.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1391 0 10288 10290 10292 10294 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll13.2.2.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1392 1 10289 10291 10293 10295 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll13.2.2.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
end
end TrainVerify.Denote.GeneratedPatterns
