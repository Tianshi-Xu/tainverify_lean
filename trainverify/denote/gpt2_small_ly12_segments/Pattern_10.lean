/- Auto-generated pattern proof file.
   Pattern: 10
   Hash: 6f2128dfb677e726
   Goals: 12, 37, 60, 85, 162, 164, 189
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_10_goalIds : List Nat := [12, 37, 60, 85, 162, 164, 189]
inductive pattern_10_target : Prop → Prop
  | goal_12 : pattern_10_target goal_12_stmt
  | goal_37 : pattern_10_target goal_37_stmt
  | goal_60 : pattern_10_target goal_60_stmt
  | goal_85 : pattern_10_target goal_85_stmt
  | goal_162 : pattern_10_target goal_162_stmt
  | goal_164 : pattern_10_target goal_164_stmt
  | goal_189 : pattern_10_target goal_189_stmt

def pattern_10_stmt : Prop :=
  ∀ {target : Prop}, pattern_10_target target → target
theorem prove_pattern_10 : pattern_10_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

