/- Goal 4 faithful layer-16 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL16Attention
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l16_norm_from_attention
    (initSM initPM : Store)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hA16 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l16_zigzag_moe_norm_from_attention_output initSM initPM hInit1 hA16
end
end TrainVerify.Denote.GeneratedPatterns
