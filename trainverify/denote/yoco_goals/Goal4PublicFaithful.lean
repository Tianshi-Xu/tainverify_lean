/- Public faithful closure for Goal 4 from external inputs only. -/
import denote.yoco_goals.Goal4PublicFaithfulLateAncestry

set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote.GeneratedGoals

/-- Complete Goal-4 faithful theorem. Late ancestry is reconstructed from the
finite external shape/init/value classes and packed-CU contracts. -/
theorem prove_goal_4_full : goal_4_stmt_full := by
  intro initSM initPM hSM hPM hInit hContract
  exact canonical_goal_4_from_late_ancestry initSM initPM hSM hPM hInit hContract
    (goal4_late_ancestry_of_external initSM initPM hSM hPM hInit hContract)

namespace Goal4PublicFaithful

/-- Public Pattern-4 entry point under faithful distributed semantics. -/
theorem prove_pattern_4 : goal_4_stmt_full := prove_goal_4_full

end Goal4PublicFaithful
end TrainVerify.Denote.GeneratedPatterns
