/- Goal 4 faithful layer-13 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL13Norm
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l13_router_from_norm
    (initSM initPM : Store)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hN13 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5784)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10280)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10281)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
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
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact l13_zigzag_moe_router_all_from_norm_input initSM initPM hPM1 hInit1 hN13
end
end TrainVerify.Denote.GeneratedPatterns
