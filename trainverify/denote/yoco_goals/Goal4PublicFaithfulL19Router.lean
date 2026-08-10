/- Goal 4 faithful layer-19 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL19Norm
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l19_router_from_norm
    (initSM initPM : Store)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hN19 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6108)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11204)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11205)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
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
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact l19_zigzag_moe_router_all_from_norm_input initSM initPM hPM1 hInit1 hN19
end
end TrainVerify.Denote.GeneratedPatterns
