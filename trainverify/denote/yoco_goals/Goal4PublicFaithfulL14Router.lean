/- Goal 4 faithful layer-14 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL14Norm
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l14_router_from_norm
    (initSM initPM : Store)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hN14 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5838)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10434)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10435)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
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
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  exact l14_zigzag_moe_router_all_from_norm_input initSM initPM hPM1 hInit1 hN14
end
end TrainVerify.Denote.GeneratedPatterns
