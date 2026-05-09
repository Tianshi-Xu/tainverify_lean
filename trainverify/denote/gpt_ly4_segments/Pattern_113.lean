/- Auto-generated pattern proof file.
   Pattern: 113
   Hash: f3f43d2b370f1260
   Goals: 210, 213, 245, 248
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7
import denote.gpt_ly4_segments.SegmentPattern_8

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_113_goalIds : List Nat := [210, 213, 245, 248]
inductive pattern_113_target : Prop → Prop
  | goal_210 : pattern_113_target goal_210_stmt
  | goal_213 : pattern_113_target goal_213_stmt
  | goal_245 : pattern_113_target goal_245_stmt
  | goal_248 : pattern_113_target goal_248_stmt

def pattern_113_stmt : Prop :=
  ∀ {target : Prop}, pattern_113_target target → target
theorem prove_pattern_113 : pattern_113_stmt := by
  intro target h
  cases h with
  | goal_210 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_3
      exact hs.right.right.right.right.right.right.left
  | goal_213 =>
      have hs := prove_segment_pattern_8 segment_pattern_8_target.inst_3
      exact hs.right.left
  | goal_245 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_4
      exact hs.right.right.right.right.right.right.left
  | goal_248 =>
      have hs := prove_segment_pattern_8 segment_pattern_8_target.inst_4
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

