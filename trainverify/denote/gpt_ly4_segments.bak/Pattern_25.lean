/- Auto-generated pattern proof file.
   Pattern: 25
   Hash: 6a6f481f06ef65d6
   Goals: 31, 33, 81, 82
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_1

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_25_goalIds : List Nat := [31, 33, 81, 82]
inductive pattern_25_target : Prop → Prop
  | goal_31 : pattern_25_target goal_31_stmt
  | goal_33 : pattern_25_target goal_33_stmt
  | goal_81 : pattern_25_target goal_81_stmt
  | goal_82 : pattern_25_target goal_82_stmt

def pattern_25_stmt : Prop :=
  ∀ {target : Prop}, pattern_25_target target → target
theorem prove_pattern_25 : pattern_25_stmt := by
  intro target h
  cases h with
  | goal_31 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_2
      exact hs.right.right.left
  | goal_33 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_2
      exact hs.right.right.right.right.left
  | goal_81 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_4
      exact hs.right.right.left
  | goal_82 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_4
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

