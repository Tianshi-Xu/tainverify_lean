/- Goal 4 faithful layer-15 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL15Attention
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
theorem goal4_l15_norm_from_attention
    (initSM initPM : Store)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hA15 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10584)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10589)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  exact l15_zigzag_moe_norm_from_attention_output initSM initPM hInit1 hA15
end
end TrainVerify.Denote.GeneratedPatterns
