/- Auto-generated pattern proof file.
   Pattern: 17
   Hash: 5106e488dcc69dc3
   Goals: 20
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_17_goalIds : List Nat := [20]
inductive pattern_17_target : Prop → Prop
  | goal_20 : pattern_17_target goal_20_stmt

def pattern_17_stmt : Prop :=
  ∀ {target : Prop}, pattern_17_target target → target
theorem prove_pattern_17 : pattern_17_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

