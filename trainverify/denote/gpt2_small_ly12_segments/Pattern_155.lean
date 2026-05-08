/- Auto-generated pattern proof file.
   Pattern: 155
   Hash: 2a803104e732b46c
   Goals: 432
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_155_goalIds : List Nat := [432]
inductive pattern_155_target : Prop → Prop
  | goal_432 : pattern_155_target goal_432_stmt

def pattern_155_stmt : Prop :=
  ∀ {target : Prop}, pattern_155_target target → target
theorem prove_pattern_155 : pattern_155_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

