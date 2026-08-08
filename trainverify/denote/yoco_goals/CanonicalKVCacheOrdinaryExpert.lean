/- Canonical Goal 1 cache-source ordinary expert boundary. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.FaithfulStackGather
import denote.Gather2Rel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

noncomputable section

/-- The remote-expert node has collective `replicaBuddies` semantics, so its
ordinary boundary is stated conditionally using the collective-independent
`Gather2Rel` certificate rather than incorrectly reusing `Zigzag2Rel`.
The certificate includes the exact gathered value and all output shapes. -/
theorem canonical_kv_cache_ordinary_expert_of_gather
    (initSM initPM : Store)
    (hExpert : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5573)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9656)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9657)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5573)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9656)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9657)
      [4096, 1024] [2048, 1024] :=
  { full_value := hExpert.value
    full_shape := hExpert.full_shape
    rank0_shape := hExpert.shard0_shape
    rank1_shape := hExpert.shard1_shape }

#print axioms canonical_kv_cache_ordinary_expert_of_gather

end
end TrainVerify.Denote.GeneratedPatterns
