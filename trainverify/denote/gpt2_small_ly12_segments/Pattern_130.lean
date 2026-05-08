/- Auto-generated pattern proof file.
   Pattern: 130
   Hash: b227dc374b18c4bb
   Goals: 367
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_130_goalIds : List Nat := [367]
inductive pattern_130_target : Prop → Prop
  | goal_367 : pattern_130_target goal_367_stmt

def pattern_130_stmt : Prop :=
  ∀ {target : Prop}, pattern_130_target target → target
theorem prove_pattern_130 : pattern_130_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

