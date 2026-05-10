/- Auto-generated pattern proof file.
   Pattern: 102
   Hash: bd1ff169297e3ea4
   Goals: 192
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_102_goalIds : List Nat := [192]
inductive pattern_102_target : Prop → Prop
  | goal_192 : pattern_102_target goal_192_stmt

def pattern_102_stmt : Prop :=
  ∀ {target : Prop}, pattern_102_target target → target
theorem prove_pattern_102 : pattern_102_stmt := by
  intro target h
  cases h with
  | goal_192 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_3
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

