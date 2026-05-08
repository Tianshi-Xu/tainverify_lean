/- Auto-generated pattern proof file.
   Pattern: 14
   Hash: 815ae0c2065c8ccf
   Goals: 17, 267
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_14_goalIds : List Nat := [17, 267]
inductive pattern_14_target : Prop → Prop
  | goal_17 : pattern_14_target goal_17_stmt
  | goal_267 : pattern_14_target goal_267_stmt

def pattern_14_stmt : Prop :=
  ∀ {target : Prop}, pattern_14_target target → target
theorem prove_pattern_14 : pattern_14_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

