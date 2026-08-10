/- Goal 4 faithful layer-12 output checkpoint. -/
import denote.yoco_goals.Goal4PublicFaithfulCheckpoint

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

structure Goal4L12OutputCheckpoint (initSM initPM : Store) : Prop where
  base : Goal4L12Checkpoint initSM initPM
  output12 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5653)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9904)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9905)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024]

theorem goal4_l12_output_checkpoint_of_external
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_4InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_4InitEnv)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM) :
    Goal4L12OutputCheckpoint initSM initPM := by
  have hSM1 := goal4_goal1_sm_shapes initSM initPM hInit
  have hPM1 := goal4_goal1_pm_shapes initSM initPM hInit
  have hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM := hInit
  have hAttention := goal4_l12_attention_checkpoint_of_external initSM initPM hInit hContract
  exact {
    base := goal4_l12_checkpoint_of_external initSM initPM hSM hPM hInit hContract
    output12 := l12_zigzag_moe_output_from_attention_output
      initSM initPM hSM1 hPM1 hInit1 hAttention.attention12
  }

end
end TrainVerify.Denote.GeneratedPatterns
