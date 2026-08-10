/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.Instances

/-!
# Corrected YOCO-MoE main theorem

This module composes exactly the claims currently exposed by the public proof
surface:

* exact ancestry-closed full statements for Goals 1, 2, 3, and 5;
* Goal 4 only at its currently public cut tier. Its stronger
  `canonical_goal_4_from_late_ancestry` theorem is an internal conditional
  closure, not a public `goal_4_stmt_full` result;
The legacy cut corpus and its witness bookkeeping remain in the standalone
`YocoMoE_MainSummary.lean`, which is the only aggregate that imports old
`Pattern_3`.
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote.GeneratedPatternInstances

namespace TrainVerify.Denote.YocoMoE.CorrectedMain
noncomputable section

/-- Honest mixed public tier: Goals 1/2/3/5 have their exact ancestry-closed
full statements, while Goal 4 remains explicitly cut-only.  No theorem in this
aggregate anticipates the unfinished Goal-4 public full closure. -/
def HonestPatternTier : Prop :=
  goal_1_stmt_full ∧
  goal_2_stmt_full ∧
  goal_3_stmt_full ∧
  goal_4_stmt_cut ∧
  goal_5_stmt_full


/-- The public mixed tier is sorry-free and preserves each theorem's real
strength: full for 1/2/3/5, cut for 4. -/
theorem honest_pattern_tier : HonestPatternTier := by
  exact ⟨prove_goal_1_from_pattern_1,
    prove_goal_2_from_pattern_2,
    prove_goal_3_from_pattern_3,
    prove_goal_4_from_pattern_4,
    prove_goal_5_from_pattern_5⟩

/-- Corrected public YOCO summary.  The full statements retain their explicit
caller contracts; this theorem does not claim a joint witness for those
assumptions. Legacy cut-tier witnesses remain isolated in
`YocoMoE_MainSummary.lean`. -/
theorem yoco_moe_corrected_main : HonestPatternTier :=
  honest_pattern_tier

end
end TrainVerify.Denote.YocoMoE.CorrectedMain
