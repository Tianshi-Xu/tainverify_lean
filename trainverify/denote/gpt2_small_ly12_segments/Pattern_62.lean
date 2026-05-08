/- Auto-generated pattern proof file.
   Pattern: 62
   Hash: f0773f1948ddccad
   Goals: 142, 167
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_62_goalIds : List Nat := [142, 167]
inductive pattern_62_target : Prop → Prop
  | goal_142 : pattern_62_target goal_142_stmt
  | goal_167 : pattern_62_target goal_167_stmt

def pattern_62_stmt : Prop :=
  ∀ {target : Prop}, pattern_62_target target → target
theorem prove_pattern_62 : pattern_62_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

