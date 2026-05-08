/- Auto-generated pattern proof file.
   Pattern: 20
   Hash: 636e2544da31dfa4
   Goals: 23, 173, 273, 298
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_20_goalIds : List Nat := [23, 173, 273, 298]
inductive pattern_20_target : Prop → Prop
  | goal_23 : pattern_20_target goal_23_stmt
  | goal_173 : pattern_20_target goal_173_stmt
  | goal_273 : pattern_20_target goal_273_stmt
  | goal_298 : pattern_20_target goal_298_stmt

def pattern_20_stmt : Prop :=
  ∀ {target : Prop}, pattern_20_target target → target
theorem prove_pattern_20 : pattern_20_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

