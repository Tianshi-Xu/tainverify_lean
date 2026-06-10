/- Auto-generated pattern proof file.
   Pattern: 16
   Hash: 5106e488dcc69dc3
   Goals: 20
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_16_goalIds : List Nat := [20]
inductive pattern_16_target : Prop → Prop
  | goal_20 : pattern_16_target goal_20_stmt

def pattern_16_stmt : Prop :=
  ∀ {target : Prop}, pattern_16_target target → target

theorem prove_pattern_16 : pattern_16_stmt := by
  intro target h
  cases h
  -- goal_20 is the 1st conjunct of segment_pattern_3_instance_1_stmt
  -- (goals 20, 21, 22, 23, 24, 25, 26, 27).
  have hseg := prove_segment_pattern_3 segment_pattern_3_target.inst_1
  exact hseg.left

end TrainVerify.Denote.GeneratedPatterns

