/- Auto-generated pattern proof file.
   Pattern: 130
   Hash: 05d53b83208ff068
   Goals: 262, 264, 278, 294, 308
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_130_goalIds : List Nat := [262, 264, 278, 294, 308]
inductive pattern_130_target : Prop → Prop
  | goal_262 : pattern_130_target goal_262_stmt
  | goal_264 : pattern_130_target goal_264_stmt
  | goal_278 : pattern_130_target goal_278_stmt
  | goal_294 : pattern_130_target goal_294_stmt
  | goal_308 : pattern_130_target goal_308_stmt

def pattern_130_stmt : Prop :=
  ∀ {target : Prop}, pattern_130_target target → target
theorem prove_pattern_130 : pattern_130_stmt := by
  intro target h
  cases h with
  | goal_262 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_1
      exact hs.right.right.right.right.right.left
  | goal_264 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_1
      exact hs.right.right.right.right.right.right.right
  | goal_278 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_2
      exact hs.right.right.right.right.right.right.right
  | goal_294 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_3
      exact hs.right.left
  | goal_308 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_4
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

