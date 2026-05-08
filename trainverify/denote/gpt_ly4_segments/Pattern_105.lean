/- Auto-generated pattern proof file.
   Pattern: 105
   Hash: dc9e058cbda65265
   Goals: 197
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_105_goalIds : List Nat := [197]
inductive pattern_105_target : Prop → Prop
  | goal_197 : pattern_105_target goal_197_stmt

def pattern_105_stmt : Prop :=
  ∀ {target : Prop}, pattern_105_target target → target
theorem prove_pattern_105 : pattern_105_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

