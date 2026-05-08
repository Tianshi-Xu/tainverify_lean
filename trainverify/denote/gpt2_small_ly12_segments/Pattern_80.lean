/- Auto-generated pattern proof file.
   Pattern: 80
   Hash: 949833158e2d742d
   Goals: 243
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_80_goalIds : List Nat := [243]
inductive pattern_80_target : Prop → Prop
  | goal_243 : pattern_80_target goal_243_stmt

def pattern_80_stmt : Prop :=
  ∀ {target : Prop}, pattern_80_target target → target
theorem prove_pattern_80 : pattern_80_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

