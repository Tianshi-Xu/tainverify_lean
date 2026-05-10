/- Auto-generated pattern proof file.
   Pattern: 29
   Hash: 971919ad0409dd0d
   Goals: 42, 92
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_29_goalIds : List Nat := [42, 92]
inductive pattern_29_target : Prop → Prop
  | goal_42 : pattern_29_target goal_42_stmt
  | goal_92 : pattern_29_target goal_92_stmt

def pattern_29_stmt : Prop :=
  ∀ {target : Prop}, pattern_29_target target → target
theorem prove_pattern_29 : pattern_29_stmt := by
  intro target h
  cases h with
  | goal_42 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_2
      exact hs.right.right.right.right.right.left
  | goal_92 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_4
      exact hs.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

