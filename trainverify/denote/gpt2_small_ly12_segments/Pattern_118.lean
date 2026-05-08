/- Auto-generated pattern proof file.
   Pattern: 118
   Hash: d94396f9bc6e75cf
   Goals: 345, 371, 476, 581
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_118_goalIds : List Nat := [345, 371, 476, 581]
inductive pattern_118_target : Prop → Prop
  | goal_345 : pattern_118_target goal_345_stmt
  | goal_371 : pattern_118_target goal_371_stmt
  | goal_476 : pattern_118_target goal_476_stmt
  | goal_581 : pattern_118_target goal_581_stmt

def pattern_118_stmt : Prop :=
  ∀ {target : Prop}, pattern_118_target target → target
theorem prove_pattern_118 : pattern_118_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

