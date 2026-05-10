/- Auto-generated pattern proof file.
   Pattern: 11
   Hash: c7dd4a63a6fafe17
   Goals: 15
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_11_goalIds : List Nat := [15]
inductive pattern_11_target : Prop → Prop
  | goal_15 : pattern_11_target goal_15_stmt

def pattern_11_stmt : Prop :=
  ∀ {target : Prop}, pattern_11_target target → target
theorem prove_pattern_11 : pattern_11_stmt := by
  intro target h
  cases h with
  | goal_15 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_1
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

