/- Goal 4 faithful layer-15 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL15Output
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l15_score_from_router
    (initSM initPM : Store)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (hAll15 :
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5896)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10598)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10599)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5897)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10600)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10601)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5895)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10596)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10597)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5898)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10602)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10603)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact goal1_gate_scores_of_logits hAll15.2.2 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 698 0 5895 5896 5897 5898 4096 (by native_decide) (by native_decide) (by decide) (by decide) hAll15.2.2.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1543 0 10596 10598 10600 10602 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll15.2.2.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1544 1 10597 10599 10601 10603 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll15.2.2.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
end
end TrainVerify.Denote.GeneratedPatterns
