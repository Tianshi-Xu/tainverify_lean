/- Auto-generated pattern proof file.
   Pattern: 10
   Hash: 6f2128dfb677e726
   Goals: 12, 37, 60, 85
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_1
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_10_goalIds : List Nat := [12, 37, 60, 85]
inductive pattern_10_target : Prop → Prop
  | goal_12 : pattern_10_target goal_12_stmt
  | goal_37 : pattern_10_target goal_37_stmt
  | goal_60 : pattern_10_target goal_60_stmt
  | goal_85 : pattern_10_target goal_85_stmt

def pattern_10_stmt : Prop :=
  ∀ {target : Prop}, pattern_10_target target → target
theorem prove_pattern_10 : pattern_10_stmt := by
  intro target h
  cases h with
  | goal_12 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_1
      exact hs.left
  | goal_37 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_2
      exact hs.left
  | goal_60 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_3
      exact hs.right.right.right.right.right.right.left
  | goal_85 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_4
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

