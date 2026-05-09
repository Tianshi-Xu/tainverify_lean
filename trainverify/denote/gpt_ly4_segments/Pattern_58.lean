/- Auto-generated pattern proof file.
   Pattern: 58
   Hash: aac94f9507845964
   Goals: 112, 138, 147, 173, 182, 208, 217, 243, 252
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_58_goalIds : List Nat := [112, 138, 147, 173, 182, 208, 217, 243, 252]
inductive pattern_58_target : Prop → Prop
  | goal_112 : pattern_58_target goal_112_stmt
  | goal_138 : pattern_58_target goal_138_stmt
  | goal_147 : pattern_58_target goal_147_stmt
  | goal_173 : pattern_58_target goal_173_stmt
  | goal_182 : pattern_58_target goal_182_stmt
  | goal_208 : pattern_58_target goal_208_stmt
  | goal_217 : pattern_58_target goal_217_stmt
  | goal_243 : pattern_58_target goal_243_stmt
  | goal_252 : pattern_58_target goal_252_stmt

def pattern_58_stmt : Prop :=
  ∀ {target : Prop}, pattern_58_target target → target
theorem prove_pattern_58 : pattern_58_stmt := by
  intro target h
  cases h with
  | goal_112 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_1
      exact hs.right.right.left
  | goal_138 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_1
      exact hs.right.right.right.right.left
  | goal_147 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_2
      exact hs.right.right.left
  | goal_173 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_2
      exact hs.right.right.right.right.left
  | goal_182 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_3
      exact hs.right.right.left
  | goal_208 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_3
      exact hs.right.right.right.right.left
  | goal_217 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_4
      exact hs.right.right.left
  | goal_243 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_4
      exact hs.right.right.right.right.left
  | goal_252 => sorry

end TrainVerify.Denote.GeneratedPatterns

