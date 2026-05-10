/- Auto-generated pattern proof file.
   Pattern: 138
   Hash: 135ec5f47a1ed74c
   Goals: 288, 298, 302, 312
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_138_goalIds : List Nat := [288, 298, 302, 312]
inductive pattern_138_target : Prop → Prop
  | goal_288 : pattern_138_target goal_288_stmt
  | goal_298 : pattern_138_target goal_298_stmt
  | goal_302 : pattern_138_target goal_302_stmt
  | goal_312 : pattern_138_target goal_312_stmt

def pattern_138_stmt : Prop :=
  ∀ {target : Prop}, pattern_138_target target → target
theorem prove_pattern_138 : pattern_138_stmt := by
  intro target h
  cases h with
  | goal_288 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_3
      exact hs.right.right.right.left
  | goal_298 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_3
      exact hs.right.right.right.right.right
  | goal_302 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_4
      exact hs.right.right.right.left
  | goal_312 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_4
      exact hs.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

