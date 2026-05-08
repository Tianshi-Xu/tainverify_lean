/- Auto-generated pattern proof file.
   Pattern: 15
   Hash: 453513444068c2dd
   Goals: 18
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_15_goalIds : List Nat := [18]
inductive pattern_15_target : Prop → Prop
  | goal_18 : pattern_15_target goal_18_stmt

def pattern_15_stmt : Prop :=
  ∀ {target : Prop}, pattern_15_target target → target
theorem prove_pattern_15 : pattern_15_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

