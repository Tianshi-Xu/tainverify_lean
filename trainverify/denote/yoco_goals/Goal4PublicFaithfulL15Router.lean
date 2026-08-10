/- Goal 4 faithful layer-15 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL15Norm
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l15_router_from_norm
    (initSM initPM : Store)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hN15 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10589)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
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
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact l15_zigzag_moe_router_all_from_norm_input initSM initPM hPM1 hInit1 hN15
end
end TrainVerify.Denote.GeneratedPatterns
