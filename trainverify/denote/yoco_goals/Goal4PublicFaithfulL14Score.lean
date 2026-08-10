/- Goal 4 faithful layer-14 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL14Output
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l14_score_from_router
    (initSM initPM : Store)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (hAll14 :
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5842)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10444)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10445)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5843)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10446)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10447)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5841)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10442)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10443)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5844)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10448)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10449)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact goal1_gate_scores_of_logits hAll14.2.2 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 663 0 5841 5842 5843 5844 4096 (by native_decide) (by native_decide) (by decide) (by decide) hAll14.2.2.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1467 0 10442 10444 10446 10448 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll14.2.2.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1468 1 10443 10445 10447 10449 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll14.2.2.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
end
end TrainVerify.Denote.GeneratedPatterns
