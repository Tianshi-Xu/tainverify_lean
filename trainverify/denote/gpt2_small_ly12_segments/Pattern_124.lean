/- Auto-generated pattern proof file.
   Pattern: 124
   Hash: 822bcf4ecfb0936c
   Goals: 361
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_124_goalIds : List Nat := [361]
inductive pattern_124_target : Prop → Prop
  | goal_361 : pattern_124_target goal_361_stmt

def pattern_124_stmt : Prop :=
  ∀ {target : Prop}, pattern_124_target target → target
theorem prove_pattern_124 : pattern_124_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

