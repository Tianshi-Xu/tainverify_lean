/- Auto-generated pattern proof file.
   Pattern: 152
   Hash: 4e07ca3b913e473b
   Goals: 419, 559, 699
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_152_goalIds : List Nat := [419, 559, 699]
inductive pattern_152_target : Prop → Prop
  | goal_419 : pattern_152_target goal_419_stmt
  | goal_559 : pattern_152_target goal_559_stmt
  | goal_699 : pattern_152_target goal_699_stmt

def pattern_152_stmt : Prop :=
  ∀ {target : Prop}, pattern_152_target target → target
theorem prove_pattern_152 : pattern_152_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

