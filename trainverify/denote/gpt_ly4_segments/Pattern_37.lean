/- Auto-generated pattern proof file.
   Pattern: 37
   Hash: e5d4d61eeb799187
   Goals: 65
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_37_goalIds : List Nat := [65]
inductive pattern_37_target : Prop → Prop
  | goal_65 : pattern_37_target goal_65_stmt

def pattern_37_stmt : Prop :=
  ∀ {target : Prop}, pattern_37_target target → target
theorem prove_pattern_37 : pattern_37_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

