/- Auto-generated pattern proof file.
   Pattern: 182
   Hash: ed0b076f0e1a7494
   Goals: 552, 727
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_182_goalIds : List Nat := [552, 727]
inductive pattern_182_target : Prop → Prop
  | goal_552 : pattern_182_target goal_552_stmt
  | goal_727 : pattern_182_target goal_727_stmt

def pattern_182_stmt : Prop :=
  ∀ {target : Prop}, pattern_182_target target → target
theorem prove_pattern_182 : pattern_182_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

