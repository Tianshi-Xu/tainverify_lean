/- Auto-generated pattern proof file.
   Pattern: 9
   Hash: e28141bffb9a2f8d
   Goals: 10, 14, 39, 62, 87
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_1
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_9_goalIds : List Nat := [10, 14, 39, 62, 87]
inductive pattern_9_target : Prop → Prop
  | goal_10 : pattern_9_target goal_10_stmt
  | goal_14 : pattern_9_target goal_14_stmt
  | goal_39 : pattern_9_target goal_39_stmt
  | goal_62 : pattern_9_target goal_62_stmt
  | goal_87 : pattern_9_target goal_87_stmt

def pattern_9_stmt : Prop :=
  ∀ {target : Prop}, pattern_9_target target → target
theorem prove_pattern_9 : pattern_9_stmt := by
  intro target h
  cases h with
  | goal_10 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_1
      exact hs.right.right.right.right.right.right.left
  | goal_14 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_1
      exact hs.right.right.left
  | goal_39 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_2
      exact hs.right.right.left
  | goal_62 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_3
      exact hs.left
  | goal_87 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_4
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

