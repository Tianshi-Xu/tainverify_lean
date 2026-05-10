/- Auto-generated pattern proof file.
   Pattern: 59
   Hash: 54d8683296d854fe
   Goals: 113, 139, 148, 174, 183, 209, 218, 244, 253
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_59_goalIds : List Nat := [113, 139, 148, 174, 183, 209, 218, 244, 253]
inductive pattern_59_target : Prop → Prop
  | goal_113 : pattern_59_target goal_113_stmt
  | goal_139 : pattern_59_target goal_139_stmt
  | goal_148 : pattern_59_target goal_148_stmt
  | goal_174 : pattern_59_target goal_174_stmt
  | goal_183 : pattern_59_target goal_183_stmt
  | goal_209 : pattern_59_target goal_209_stmt
  | goal_218 : pattern_59_target goal_218_stmt
  | goal_244 : pattern_59_target goal_244_stmt
  | goal_253 : pattern_59_target goal_253_stmt

def pattern_59_stmt : Prop :=
  ∀ {target : Prop}, pattern_59_target target → target
theorem prove_pattern_59 : pattern_59_stmt := by
  intro target h
  cases h with
  | goal_113 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_1
      exact hs.right.right.right.left
  | goal_139 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_1
      exact hs.right.right.right.right.right.left
  | goal_148 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_2
      exact hs.right.right.right.left
  | goal_174 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_2
      exact hs.right.right.right.right.right.left
  | goal_183 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_3
      exact hs.right.right.right.left
  | goal_209 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_3
      exact hs.right.right.right.right.right.left
  | goal_218 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_4
      exact hs.right.right.right.left
  | goal_244 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_4
      exact hs.right.right.right.right.right.left
  | goal_253 => sorry

end TrainVerify.Denote.GeneratedPatterns

