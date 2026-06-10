/- Auto-generated pattern proof file.
   Pattern: 112
   Hash: 810a701986593b44
   Goals: 206, 215, 241, 250
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_112_goalIds : List Nat := [206, 215, 241, 250]
inductive pattern_112_target : Prop → Prop
  | goal_206 : pattern_112_target goal_206_stmt
  | goal_215 : pattern_112_target goal_215_stmt
  | goal_241 : pattern_112_target goal_241_stmt
  | goal_250 : pattern_112_target goal_250_stmt

def pattern_112_stmt : Prop :=
  ∀ {target : Prop}, pattern_112_target target → target
theorem prove_pattern_112 : pattern_112_stmt := by
  intro target h
  cases h with
  | goal_206 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_3
      exact hs.right.right.left
  | goal_215 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_4
      exact hs.left
  | goal_241 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_4
      exact hs.right.right.left
  | goal_250 => sorry

end TrainVerify.Denote.GeneratedPatterns

