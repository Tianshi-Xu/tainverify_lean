/- Auto-generated pattern proof file.
   Pattern: 129
   Hash: 728f1d55e9e12045
   Goals: 261, 263, 277, 293, 307
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_129_goalIds : List Nat := [261, 263, 277, 293, 307]
inductive pattern_129_target : Prop → Prop
  | goal_261 : pattern_129_target goal_261_stmt
  | goal_263 : pattern_129_target goal_263_stmt
  | goal_277 : pattern_129_target goal_277_stmt
  | goal_293 : pattern_129_target goal_293_stmt
  | goal_307 : pattern_129_target goal_307_stmt

def pattern_129_stmt : Prop :=
  ∀ {target : Prop}, pattern_129_target target → target

theorem prove_pattern_129 : pattern_129_stmt := by
  intro target h
  cases h with
  | goal_261 =>
      sorry
  | goal_263 =>
      sorry
  | goal_277 =>
      sorry
  | goal_293 =>
      sorry
  | goal_307 =>
      sorry

end TrainVerify.Denote.GeneratedPatterns
