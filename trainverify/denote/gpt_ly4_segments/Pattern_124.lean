/- Auto-generated pattern proof file.
   Pattern: 124
   Hash: 7465618b9517210c
   Goals: 237
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_124_goalIds : List Nat := [237]
inductive pattern_124_target : Prop → Prop
  | goal_237 : pattern_124_target goal_237_stmt

def pattern_124_stmt : Prop :=
  ∀ {target : Prop}, pattern_124_target target → target
theorem prove_pattern_124 : pattern_124_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

