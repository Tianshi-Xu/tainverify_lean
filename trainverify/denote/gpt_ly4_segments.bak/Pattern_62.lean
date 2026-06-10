/- Auto-generated pattern proof file.
   Pattern: 62
   Hash: 8a17453f255d6c1c
   Goals: 116, 118, 120, 151, 153, 155, 186, 188, 190, 221, 223, 225
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_62_goalIds : List Nat := [116, 118, 120, 151, 153, 155, 186, 188, 190, 221, 223, 225]
inductive pattern_62_target : Prop → Prop
  | goal_116 : pattern_62_target goal_116_stmt
  | goal_118 : pattern_62_target goal_118_stmt
  | goal_120 : pattern_62_target goal_120_stmt
  | goal_151 : pattern_62_target goal_151_stmt
  | goal_153 : pattern_62_target goal_153_stmt
  | goal_155 : pattern_62_target goal_155_stmt
  | goal_186 : pattern_62_target goal_186_stmt
  | goal_188 : pattern_62_target goal_188_stmt
  | goal_190 : pattern_62_target goal_190_stmt
  | goal_221 : pattern_62_target goal_221_stmt
  | goal_223 : pattern_62_target goal_223_stmt
  | goal_225 : pattern_62_target goal_225_stmt

def pattern_62_stmt : Prop :=
  ∀ {target : Prop}, pattern_62_target target → target
theorem prove_pattern_62 : pattern_62_stmt := by
  intro target h
  cases h with
  | goal_116 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_1
      exact hs.right.right.right.right.right.right.left
  | goal_118 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_1
      exact hs.left
  | goal_120 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_1
      exact hs.right.right.left
  | goal_151 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_2
      exact hs.right.right.right.right.right.right.left
  | goal_153 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_2
      exact hs.left
  | goal_155 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_2
      exact hs.right.right.left
  | goal_186 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_3
      exact hs.right.right.right.right.right.right.left
  | goal_188 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_3
      exact hs.left
  | goal_190 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_3
      exact hs.right.right.left
  | goal_221 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_4
      exact hs.right.right.right.right.right.right.left
  | goal_223 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_4
      exact hs.left
  | goal_225 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_4
      exact hs.right.right.left

end TrainVerify.Denote.GeneratedPatterns

