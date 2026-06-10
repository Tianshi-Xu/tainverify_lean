/- Auto-generated pattern proof file.
   Pattern: 46
   Hash: 7c52e5bc0cd0d2e6
   Goals: 77, 102
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_46_goalIds : List Nat := [77, 102]
inductive pattern_46_target : Prop → Prop
  | goal_77 : pattern_46_target goal_77_stmt
  | goal_102 : pattern_46_target goal_102_stmt

def pattern_46_stmt : Prop :=
  ∀ {target : Prop}, pattern_46_target target → target
theorem prove_pattern_46 : pattern_46_stmt := by
  intro target h
  cases h with
  | goal_77 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_3
      exact hs.right.right.right.right.right.right.right
  | goal_102 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_4
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

