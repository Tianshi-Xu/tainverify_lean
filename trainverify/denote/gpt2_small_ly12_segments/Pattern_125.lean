/- Auto-generated pattern proof file.
   Pattern: 125
   Hash: fe11c89e05945b6a
   Goals: 362
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_125_goalIds : List Nat := [362]
inductive pattern_125_target : Prop → Prop
  | goal_362 : pattern_125_target goal_362_stmt

def pattern_125_stmt : Prop :=
  ∀ {target : Prop}, pattern_125_target target → target
theorem prove_pattern_125 : pattern_125_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

