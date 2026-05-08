/- Auto-generated pattern proof file.
   Pattern: 214
   Hash: c362b37e8ea68259
   Goals: 750, 754, 796, 838
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_214_goalIds : List Nat := [750, 754, 796, 838]
inductive pattern_214_target : Prop → Prop
  | goal_750 : pattern_214_target goal_750_stmt
  | goal_754 : pattern_214_target goal_754_stmt
  | goal_796 : pattern_214_target goal_796_stmt
  | goal_838 : pattern_214_target goal_838_stmt

def pattern_214_stmt : Prop :=
  ∀ {target : Prop}, pattern_214_target target → target
theorem prove_pattern_214 : pattern_214_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

