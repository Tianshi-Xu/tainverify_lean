/- Auto-generated pattern proof file.
   Pattern: 153
   Hash: 5ee1d6a502ef74c1
   Goals: 427
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_153_goalIds : List Nat := [427]
inductive pattern_153_target : Prop → Prop
  | goal_427 : pattern_153_target goal_427_stmt

def pattern_153_stmt : Prop :=
  ∀ {target : Prop}, pattern_153_target target → target
theorem prove_pattern_153 : pattern_153_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

