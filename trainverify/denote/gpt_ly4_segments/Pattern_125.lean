/- Auto-generated pattern proof file.
   Pattern: 125
   Hash: 9df962180fe72704
   Goals: 251, 258, 268, 272, 282, 286, 296, 300, 310
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_125_goalIds : List Nat := [251, 258, 268, 272, 282, 286, 296, 300, 310]
inductive pattern_125_target : Prop → Prop
  | goal_251 : pattern_125_target goal_251_stmt
  | goal_258 : pattern_125_target goal_258_stmt
  | goal_268 : pattern_125_target goal_268_stmt
  | goal_272 : pattern_125_target goal_272_stmt
  | goal_282 : pattern_125_target goal_282_stmt
  | goal_286 : pattern_125_target goal_286_stmt
  | goal_296 : pattern_125_target goal_296_stmt
  | goal_300 : pattern_125_target goal_300_stmt
  | goal_310 : pattern_125_target goal_310_stmt

def pattern_125_stmt : Prop :=
  ∀ {target : Prop}, pattern_125_target target → target
theorem prove_pattern_125 : pattern_125_stmt := by
  intro target h
  cases h with
  | goal_251 => sorry
  | goal_258 =>
      sorry
  | goal_268 =>
      sorry
  | goal_272 =>
      sorry
  | goal_282 =>
      sorry
  | goal_286 =>
      sorry
  | goal_296 =>
      sorry
  | goal_300 =>
      sorry
  | goal_310 =>
      sorry

end TrainVerify.Denote.GeneratedPatterns

