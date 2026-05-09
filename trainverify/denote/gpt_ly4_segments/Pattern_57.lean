/- Auto-generated pattern proof file.
   Pattern: 57
   Hash: 87e3e47c8d323ee4
   Goals: 111, 137, 146
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_57_goalIds : List Nat := [111, 137, 146]
inductive pattern_57_target : Prop → Prop
  | goal_111 : pattern_57_target goal_111_stmt
  | goal_137 : pattern_57_target goal_137_stmt
  | goal_146 : pattern_57_target goal_146_stmt

def pattern_57_stmt : Prop :=
  ∀ {target : Prop}, pattern_57_target target → target
theorem prove_pattern_57 : pattern_57_stmt := by
  intro target h
  cases h with
  | goal_111 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_1
      exact hs.right.left
  | goal_137 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_1
      exact hs.right.right.right.left
  | goal_146 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_2
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

