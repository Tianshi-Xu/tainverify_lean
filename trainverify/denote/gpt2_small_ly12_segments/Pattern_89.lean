/- Auto-generated pattern proof file.
   Pattern: 89
   Hash: 25c9e5f3e278d543
   Goals: 308
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_89_goalIds : List Nat := [308]
inductive pattern_89_target : Prop → Prop
  | goal_308 : pattern_89_target goal_308_stmt

def pattern_89_stmt : Prop :=
  ∀ {target : Prop}, pattern_89_target target → target
theorem prove_pattern_89 : pattern_89_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

