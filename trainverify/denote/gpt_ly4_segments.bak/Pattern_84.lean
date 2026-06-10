/- Auto-generated pattern proof file.
   Pattern: 84
   Hash: 782f341d1dcbc271
   Goals: 150, 154, 220, 222, 276, 280, 304, 306
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_5
import denote.gpt_ly4_segments.SegmentPattern_9
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_84_goalIds : List Nat := [150, 154, 220, 222, 276, 280, 304, 306]
inductive pattern_84_target : Prop → Prop
  | goal_150 : pattern_84_target goal_150_stmt
  | goal_154 : pattern_84_target goal_154_stmt
  | goal_220 : pattern_84_target goal_220_stmt
  | goal_222 : pattern_84_target goal_222_stmt
  | goal_276 : pattern_84_target goal_276_stmt
  | goal_280 : pattern_84_target goal_280_stmt
  | goal_304 : pattern_84_target goal_304_stmt
  | goal_306 : pattern_84_target goal_306_stmt

def pattern_84_stmt : Prop :=
  ∀ {target : Prop}, pattern_84_target target → target
theorem prove_pattern_84 : pattern_84_stmt := by
  intro target h
  cases h with
  | goal_150 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_2
      exact hs.right.right.right.right.right.left
  | goal_154 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_2
      exact hs.right.left
  | goal_220 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_4
      exact hs.right.right.right.right.right.left
  | goal_222 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_4
      exact hs.right.right.right.right.right.right.right
  | goal_276 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_2
      exact hs.right.right.right.right.right.left
  | goal_280 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_2
      exact hs.right.left
  | goal_304 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_4
      exact hs.right.right.right.right.right.left
  | goal_306 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_4
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

