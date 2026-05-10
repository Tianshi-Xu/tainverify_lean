/- Auto-generated pattern proof file.
   Pattern: 76
   Hash: 9ccba3af8a3158d9
   Goals: 135, 141, 176, 179, 255
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7
import denote.gpt_ly4_segments.SegmentPattern_8

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_76_goalIds : List Nat := [135, 141, 176, 179, 255]
inductive pattern_76_target : Prop → Prop
  | goal_135 : pattern_76_target goal_135_stmt
  | goal_141 : pattern_76_target goal_141_stmt
  | goal_176 : pattern_76_target goal_176_stmt
  | goal_179 : pattern_76_target goal_179_stmt
  | goal_255 : pattern_76_target goal_255_stmt

def pattern_76_stmt : Prop :=
  ∀ {target : Prop}, pattern_76_target target → target
theorem prove_pattern_76 : pattern_76_stmt := by
  intro target h
  cases h with
  | goal_135 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_1
      exact hs.right.left
  | goal_141 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_1
      exact hs.right.right.right.right.right.right.right
  | goal_176 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_2
      exact hs.right.right.right.right.right.right.right
  | goal_179 =>
      have hs := prove_segment_pattern_8 segment_pattern_8_target.inst_2
      exact hs.right.right
  | goal_255 => sorry

end TrainVerify.Denote.GeneratedPatterns

