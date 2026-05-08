/- Auto-generated pattern proof file.
   Pattern: 86
   Hash: 3ace81adb4a0f428
   Goals: 157
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_86_goalIds : List Nat := [157]
inductive pattern_86_target : Prop → Prop
  | goal_157 : pattern_86_target goal_157_stmt

def pattern_86_stmt : Prop :=
  ∀ {target : Prop}, pattern_86_target target → target
theorem prove_pattern_86 : pattern_86_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

