/- Goal 4 faithful layer-18 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL18Output
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l18_score_from_router
    (initSM initPM : Store)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (hAll18 :
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6058)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11060)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11061)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6059)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11062)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11063)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] ∧
      Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6057)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11058)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11059)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6060)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11064)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11065)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact goal1_gate_scores_of_logits hAll18.2.2 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 803 0 6057 6058 6059 6060 4096 (by native_decide) (by native_decide) (by decide) (by decide) hAll18.2.2.full_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1771 0 11058 11060 11062 11064 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll18.2.2.rank0_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1772 1 11059 11061 11063 11065 2048 (by native_decide) (by native_decide) (by decide) (by decide) hAll18.2.2.rank1_shape (by native_decide) (by native_decide) (by native_decide) (by native_decide))
end
end TrainVerify.Denote.GeneratedPatterns
