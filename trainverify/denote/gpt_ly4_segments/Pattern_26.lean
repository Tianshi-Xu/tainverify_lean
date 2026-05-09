/- Auto-generated pattern proof file.
   Pattern: 26
   Hash: 8bc48b286bacd2f6
   Goals: 35, 64, 89
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_1
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_26_goalIds : List Nat := [35, 64, 89]
inductive pattern_26_target : Prop → Prop
  | goal_35 : pattern_26_target goal_35_stmt
  | goal_64 : pattern_26_target goal_64_stmt
  | goal_89 : pattern_26_target goal_89_stmt

def pattern_26_stmt : Prop :=
  ∀ {target : Prop}, pattern_26_target target → target
theorem prove_pattern_26 : pattern_26_stmt := by
  intro target h
  cases h with
  | goal_35 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_2
      exact hs.right.right.right.right.right.right.left
  | goal_64 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_3
      exact hs.right.right.left
  | goal_89 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_4
      exact hs.right.right.left

end TrainVerify.Denote.GeneratedPatterns

