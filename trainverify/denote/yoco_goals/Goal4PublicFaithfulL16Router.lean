/- Goal 4 faithful layer-16 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL16Norm
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l16_router_from_norm
    (initSM initPM : Store)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hN16 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
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
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact l16_zigzag_moe_router_all_from_norm_input initSM initPM hPM1 hInit1 hN16
end
end TrainVerify.Denote.GeneratedPatterns
