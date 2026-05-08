/- Auto-generated pattern proof file.
   Pattern: 5
   Hash: de5f5f99bf861ead
   Goals: 5, 30, 55, 75, 80, 100, 105, 125, 130, 150, 155, 175, 180, 200, 205, 225, 230, 255, 275, 280, 300
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_5_goalIds : List Nat := [5, 30, 55, 75, 80, 100, 105, 125, 130, 150, 155, 175, 180, 200, 205, 225, 230, 255, 275, 280, 300]
inductive pattern_5_target : Prop → Prop
  | goal_5 : pattern_5_target goal_5_stmt
  | goal_30 : pattern_5_target goal_30_stmt
  | goal_55 : pattern_5_target goal_55_stmt
  | goal_75 : pattern_5_target goal_75_stmt
  | goal_80 : pattern_5_target goal_80_stmt
  | goal_100 : pattern_5_target goal_100_stmt
  | goal_105 : pattern_5_target goal_105_stmt
  | goal_125 : pattern_5_target goal_125_stmt
  | goal_130 : pattern_5_target goal_130_stmt
  | goal_150 : pattern_5_target goal_150_stmt
  | goal_155 : pattern_5_target goal_155_stmt
  | goal_175 : pattern_5_target goal_175_stmt
  | goal_180 : pattern_5_target goal_180_stmt
  | goal_200 : pattern_5_target goal_200_stmt
  | goal_205 : pattern_5_target goal_205_stmt
  | goal_225 : pattern_5_target goal_225_stmt
  | goal_230 : pattern_5_target goal_230_stmt
  | goal_255 : pattern_5_target goal_255_stmt
  | goal_275 : pattern_5_target goal_275_stmt
  | goal_280 : pattern_5_target goal_280_stmt
  | goal_300 : pattern_5_target goal_300_stmt

def pattern_5_stmt : Prop :=
  ∀ {target : Prop}, pattern_5_target target → target
theorem prove_pattern_5 : pattern_5_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

