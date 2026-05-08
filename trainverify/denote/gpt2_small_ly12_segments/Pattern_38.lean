/- Auto-generated pattern proof file.
   Pattern: 38
   Hash: e5d4d61eeb799187
   Goals: 65
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_38_goalIds : List Nat := [65]
inductive pattern_38_target : Prop → Prop
  | goal_65 : pattern_38_target goal_65_stmt

def pattern_38_stmt : Prop :=
  ∀ {target : Prop}, pattern_38_target target → target
theorem prove_pattern_38 : pattern_38_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

