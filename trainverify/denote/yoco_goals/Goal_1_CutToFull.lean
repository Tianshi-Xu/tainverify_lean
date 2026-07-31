import denote.yoco_goals.Goal_1_FullRing

set_option linter.style.longLine false

namespace TrainVerify.Denote.GeneratedGoals

open TrainVerify.Denote.GeneratedPatterns

/-- Goal 1's full ring-aware theorem is stronger than the cut implication: the
full proof closes directly from the reconstructed final RMSNorm lineage and the
proved cross-entropy sharding theorem.  Hence every proved cut instance lifts,
without requiring the false claim that the mixed faithful cut is a literal
full-graph sublist. -/
theorem goal_1_cut_to_full_ringAttn (_h : goal_1_stmt_with_labels) :
    goal_1_stmt_ringAttn_full_with_labels :=
  prove_goal_1_ringAttn_full

end TrainVerify.Denote.GeneratedGoals
