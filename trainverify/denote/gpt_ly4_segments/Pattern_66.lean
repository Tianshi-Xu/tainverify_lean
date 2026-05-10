/- Auto-generated pattern proof file.
   Pattern: 66
   Hash: 80e110f2357c8703
   Goals: 123, 158, 191, 226
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_66_goalIds : List Nat := [123, 158, 191, 226]
inductive pattern_66_target : Prop → Prop
  | goal_123 : pattern_66_target goal_123_stmt
  | goal_158 : pattern_66_target goal_158_stmt
  | goal_191 : pattern_66_target goal_191_stmt
  | goal_226 : pattern_66_target goal_226_stmt

def pattern_66_stmt : Prop :=
  ∀ {target : Prop}, pattern_66_target target → target
theorem prove_pattern_66 : pattern_66_stmt := by
  intro target h
  cases h with
  | goal_123 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_1
      exact hs.right.right.right.right.right.left
  | goal_158 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_2
      exact hs.right.right.right.right.right.left
  | goal_191 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_3
      exact hs.right.right.right.left
  | goal_226 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_4
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

