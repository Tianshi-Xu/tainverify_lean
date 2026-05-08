/- Auto-generated pattern proof file.
   Pattern: 65
   Hash: 4658aa503651a990
   Goals: 152
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_65_goalIds : List Nat := [152]
inductive pattern_65_target : Prop → Prop
  | goal_152 : pattern_65_target goal_152_stmt

def pattern_65_stmt : Prop :=
  ∀ {target : Prop}, pattern_65_target target → target
theorem prove_pattern_65 : pattern_65_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

