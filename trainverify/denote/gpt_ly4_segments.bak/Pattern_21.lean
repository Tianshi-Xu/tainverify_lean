/- Auto-generated pattern proof file.
   Pattern: 21
   Hash: 0c671a7b0d6e6d62
   Goals: 25, 50, 105
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_21_goalIds : List Nat := [25, 50, 105]
inductive pattern_21_target : Prop → Prop
  | goal_25 : pattern_21_target goal_25_stmt
  | goal_50 : pattern_21_target goal_50_stmt
  | goal_105 : pattern_21_target goal_105_stmt

def pattern_21_stmt : Prop :=
  ∀ {target : Prop}, pattern_21_target target → target
theorem prove_pattern_21 : pattern_21_stmt := by
  intro target h
  cases h with
  | goal_25 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_1
      exact hs.right.right.right.right.right.left
  | goal_50 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_2
      exact hs.right.right.right.right.right.left
  | goal_105 => sorry

end TrainVerify.Denote.GeneratedPatterns

