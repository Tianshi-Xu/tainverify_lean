/- Auto-generated pattern proof file.
   Pattern: 47
   Hash: feaf0a8f2f7db76b
   Goals: 90
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_47_goalIds : List Nat := [90]
inductive pattern_47_target : Prop → Prop
  | goal_90 : pattern_47_target goal_90_stmt

def pattern_47_stmt : Prop :=
  ∀ {target : Prop}, pattern_47_target target → target
theorem prove_pattern_47 : pattern_47_stmt := by
  intro target h
  cases h with
  | goal_90 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_4
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

