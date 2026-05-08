/- Auto-generated pattern proof file.
   Pattern: 74
   Hash: f26c501d7986255d
   Goals: 193
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_74_goalIds : List Nat := [193]
inductive pattern_74_target : Prop → Prop
  | goal_193 : pattern_74_target goal_193_stmt

def pattern_74_stmt : Prop :=
  ∀ {target : Prop}, pattern_74_target target → target
theorem prove_pattern_74 : pattern_74_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

