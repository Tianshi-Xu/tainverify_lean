/- Auto-generated pattern proof file.
   Pattern: 167
   Hash: 1b8c8cb8e0b2b226
   Goals: 472, 717
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_167_goalIds : List Nat := [472, 717]
inductive pattern_167_target : Prop → Prop
  | goal_472 : pattern_167_target goal_472_stmt
  | goal_717 : pattern_167_target goal_717_stmt

def pattern_167_stmt : Prop :=
  ∀ {target : Prop}, pattern_167_target target → target
theorem prove_pattern_167 : pattern_167_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

