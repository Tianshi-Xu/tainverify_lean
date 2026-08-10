/- Canonical Goal 1, layer 12: complete faithful second zigzag block. -/
import denote.yoco_goals.CanonicalL12Block2ShardedKVAttention
import denote.yoco_goals.L12Block2ZigzagMoEComposition

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

/-- Complete faithful L12 second zigzag block.  The stream remains `Zigzag2Rel`
with canonical cu tensor 6252 throughout; the ordinary shared-cache relation is
used only to derive the mixed-layout K/V attention inputs. -/
theorem canonical_l12b2_from_incoming_and_cache (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9905)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hContract : Goal1AncestryInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5707)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hAttention :=
    canonical_l12b2_attention_residual_from_incoming_and_cache initSM initPM
      hPM hInit hIncoming hCache hContract
  exact l12b2_zigzag_moe_output_from_attention_output initSM initPM
    hSM hPM hInit hAttention

#print axioms canonical_l12b2_from_incoming_and_cache

end
end TrainVerify.Denote.GeneratedPatterns
