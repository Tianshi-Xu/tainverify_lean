/- Goal 4 faithful layer-19 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL19Output
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l19_score_from_router
    (initSM initPM : Store)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (hAll19 :
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6112)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11214)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11215)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6113)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11216)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11217)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6111)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11212)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11213)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6114)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11218)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11219)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact goal1_gate_scores_of_logits hAll19.2.2 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 838 0 6111 6112 6113 6114 4096 (by native_decide) (by native_decide) (by decide) (by decide) hAll19.2.2.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1847 0 11212 11214 11216 11218 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll19.2.2.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1848 1 11213 11215 11217 11219 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll19.2.2.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
end
end TrainVerify.Denote.GeneratedPatterns
