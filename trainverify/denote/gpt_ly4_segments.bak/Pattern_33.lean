/- Auto-generated pattern proof file.
   Pattern: 33
   Hash: 751f5da041372c5f
   Goals: 46
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_33_goalIds : List Nat := [46]
inductive pattern_33_target : Prop → Prop
  | goal_46 : pattern_33_target goal_46_stmt

def pattern_33_stmt : Prop :=
  ∀ {target : Prop}, pattern_33_target target → target
theorem prove_pattern_33 : pattern_33_stmt := by
  intro target h
  cases h with
  | goal_46 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_2
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

