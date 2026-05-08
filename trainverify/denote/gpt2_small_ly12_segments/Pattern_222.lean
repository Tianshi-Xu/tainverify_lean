/- Auto-generated pattern proof file.
   Pattern: 222
   Hash: cd4c1af3aff22a92
   Goals: 773, 787, 843, 857, 871, 899
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_222_goalIds : List Nat := [773, 787, 843, 857, 871, 899]
inductive pattern_222_target : Prop → Prop
  | goal_773 : pattern_222_target goal_773_stmt
  | goal_787 : pattern_222_target goal_787_stmt
  | goal_843 : pattern_222_target goal_843_stmt
  | goal_857 : pattern_222_target goal_857_stmt
  | goal_871 : pattern_222_target goal_871_stmt
  | goal_899 : pattern_222_target goal_899_stmt

def pattern_222_stmt : Prop :=
  ∀ {target : Prop}, pattern_222_target target → target
theorem prove_pattern_222 : pattern_222_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

