/- Auto-generated pattern proof file.
   Pattern: 180
   Hash: 6bd05cdd1f598fc7
   Goals: 541
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_180_goalIds : List Nat := [541]
inductive pattern_180_target : Prop → Prop
  | goal_541 : pattern_180_target goal_541_stmt

def pattern_180_stmt : Prop :=
  ∀ {target : Prop}, pattern_180_target target → target
theorem prove_pattern_180 : pattern_180_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

