/- Goal 4 faithful layer-17 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL17Output
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l17_score_from_router
    (initSM initPM : Store)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (hAll17 :
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6004)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10906)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10907)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6005)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10908)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10909)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6003)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10904)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10905)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6006)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10910)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10911)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact goal1_gate_scores_of_logits hAll17.2.2 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 768 0 6003 6004 6005 6006 4096 (by native_decide) (by native_decide) (by decide) (by decide) hAll17.2.2.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1695 0 10904 10906 10908 10910 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll17.2.2.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1696 1 10905 10907 10909 10911 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll17.2.2.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
end
end TrainVerify.Denote.GeneratedPatterns
