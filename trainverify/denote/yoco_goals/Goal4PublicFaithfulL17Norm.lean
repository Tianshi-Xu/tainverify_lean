/- Goal 4 faithful layer-17 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL17Attention
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l17_norm_from_attention
    (initSM initPM : Store)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hA17 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10893)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l17_zigzag_moe_norm_from_attention_output initSM initPM hInit1 hA17
end
end TrainVerify.Denote.GeneratedPatterns
