/- Auto-generated pattern proof file.
   Pattern: 34
   Hash: 4750b7077e98cb25
   Goals: 48
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_34_goalIds : List Nat := [48]
inductive pattern_34_target : Prop → Prop
  | goal_48 : pattern_34_target goal_48_stmt

def pattern_34_stmt : Prop :=
  ∀ {target : Prop}, pattern_34_target target → target
theorem prove_pattern_34 : pattern_34_stmt := by
  intro target h
  cases h with
  | goal_48 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_2
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

