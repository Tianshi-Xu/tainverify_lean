/- Goal 1: complete third zigzag block, 5707 -> 5761. -/
import denote.yoco_goals.Goal1L12Block3ShardedKVAttention
import denote.yoco_goals.Goal1L12Block3MoEComposition

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section

/-- The full real Goal-1 third zigzag block.  The only computed caller
interfaces are the incoming zigzag stream and the shared ordinary cache.
Q is zigzag, K/V are derived from the cache, and attention uses the faithful
mixed sharded-K/V collective. -/
theorem goal1_l12_third_zigzag_block
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hContract : Goal1ExternalInputContract initSM initPM)
    (hStream : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5707)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5761)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10212)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10213)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hAttention := goal1_l12_block3_attention_residual_from_stream_cache
    initSM initPM hPM hInit hContract hStream hCache
  exact goal1_l12_block3_moe_output_from_attention_output
    initSM initPM hSM hPM hInit hAttention

#print axioms goal1_l12_third_zigzag_block

end
end TrainVerify.Denote.GeneratedPatterns
