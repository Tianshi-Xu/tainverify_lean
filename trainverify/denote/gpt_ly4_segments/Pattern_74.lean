/- Auto-generated pattern proof file.
   Pattern: 74
   Hash: 67f6188cec178bd5
   Goals: 133, 168, 203, 238
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_74_goalIds : List Nat := [133, 168, 203, 238]
inductive pattern_74_target : Prop → Prop
  | goal_133 : pattern_74_target goal_133_stmt
  | goal_168 : pattern_74_target goal_168_stmt
  | goal_203 : pattern_74_target goal_203_stmt
  | goal_238 : pattern_74_target goal_238_stmt

def pattern_74_stmt : Prop :=
  ∀ {target : Prop}, pattern_74_target target → target
theorem prove_pattern_74 : pattern_74_stmt := by
  intro target h
  cases h with
  | goal_133 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_1
      exact hs.right.right.right.right.right.right.right
  | goal_168 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_2
      exact hs.right.right.right.right.right.right.right
  | goal_203 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_3
      exact hs.right.right.right.right.right.right.right
  | goal_238 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_4
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

