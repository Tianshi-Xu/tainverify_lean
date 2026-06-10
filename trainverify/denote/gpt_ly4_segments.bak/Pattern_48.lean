/- Auto-generated pattern proof file.
   Pattern: 48
   Hash: 5e0adb6ea9b6bab5
   Goals: 91
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_48_goalIds : List Nat := [91]
inductive pattern_48_target : Prop → Prop
  | goal_91 : pattern_48_target goal_91_stmt

def pattern_48_stmt : Prop :=
  ∀ {target : Prop}, pattern_48_target target → target
theorem prove_pattern_48 : pattern_48_stmt := by
  intro target h
  cases h with
  | goal_91 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_4
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

