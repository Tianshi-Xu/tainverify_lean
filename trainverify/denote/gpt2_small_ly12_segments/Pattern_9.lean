/- Auto-generated pattern proof file.
   Pattern: 9
   Hash: 43b127ef701abb72
   Goals: 10, 160, 289
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_9_goalIds : List Nat := [10, 160, 289]
inductive pattern_9_target : Prop → Prop
  | goal_10 : pattern_9_target goal_10_stmt
  | goal_160 : pattern_9_target goal_160_stmt
  | goal_289 : pattern_9_target goal_289_stmt

def pattern_9_stmt : Prop :=
  ∀ {target : Prop}, pattern_9_target target → target
theorem prove_pattern_9 : pattern_9_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

