/- Goal 4 faithful layer-18 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL18Norm
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l18_router_from_norm
    (initSM initPM : Store)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hN18 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
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
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact l18_zigzag_moe_router_all_from_norm_input initSM initPM hPM1 hInit1 hN18
end
end TrainVerify.Denote.GeneratedPatterns
