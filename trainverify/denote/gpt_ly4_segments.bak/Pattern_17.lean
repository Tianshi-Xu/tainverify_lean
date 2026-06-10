/- Auto-generated pattern proof file.
   Pattern: 17
   Hash: cbe3e5f51755a532
   Goals: 21
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_17_goalIds : List Nat := [21]
inductive pattern_17_target : Prop → Prop
  | goal_21 : pattern_17_target goal_21_stmt

def pattern_17_stmt : Prop :=
  ∀ {target : Prop}, pattern_17_target target → target
theorem prove_pattern_17 : pattern_17_stmt := by
  intro target h
  cases h with
  | goal_21 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_1
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

