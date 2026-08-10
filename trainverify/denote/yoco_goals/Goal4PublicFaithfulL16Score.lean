/- Goal 4 faithful layer-16 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL16Output
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l16_score_from_router
    (initSM initPM : Store)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (hAll16 :
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5950)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10752)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10753)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5951)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10754)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10755)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5949)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10750)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10751)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5952)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10756)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10757)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact goal1_gate_scores_of_logits hAll16.2.2 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 733 0 5949 5950 5951 5952 4096 (by native_decide) (by native_decide) (by decide) (by decide) hAll16.2.2.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1619 0 10750 10752 10754 10756 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll16.2.2.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1620 1 10751 10753 10755 10757 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll16.2.2.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
end
end TrainVerify.Denote.GeneratedPatterns
