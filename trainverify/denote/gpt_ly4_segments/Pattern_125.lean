/- Auto-generated pattern proof file.
   Pattern: 125
   Hash: 9df962180fe72704
   Goals: 251, 258, 268, 272, 282, 286, 296, 300, 310
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

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
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_1
      exact hs.right.left
  | goal_268 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_1
      exact hs.right.right.right.left
  | goal_272 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_2
      exact hs.right.left
  | goal_282 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_2
      exact hs.right.right.right.left
  | goal_286 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_3
      exact hs.right.left
  | goal_296 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_3
      exact hs.right.right.right.left
  | goal_300 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_4
      exact hs.right.left
  | goal_310 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_4
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

