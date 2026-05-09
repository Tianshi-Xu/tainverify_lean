/- Auto-generated pattern proof file.
   Pattern: 14
   Hash: 453513444068c2dd
   Goals: 18
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_14_goalIds : List Nat := [18]
inductive pattern_14_target : Prop → Prop
  | goal_18 : pattern_14_target goal_18_stmt

def pattern_14_stmt : Prop :=
  ∀ {target : Prop}, pattern_14_target target → target
theorem prove_pattern_14 : pattern_14_stmt := by
  intro target h
  cases h with
  | goal_18 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_1
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

