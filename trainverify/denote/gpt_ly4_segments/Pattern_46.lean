/- Auto-generated pattern proof file.
   Pattern: 46
   Hash: 7c52e5bc0cd0d2e6
   Goals: 77, 102
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_46_goalIds : List Nat := [77, 102]
inductive pattern_46_target : Prop → Prop
  | goal_77 : pattern_46_target goal_77_stmt
  | goal_102 : pattern_46_target goal_102_stmt

def pattern_46_stmt : Prop :=
  ∀ {target : Prop}, pattern_46_target target → target
theorem prove_pattern_46 : pattern_46_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

