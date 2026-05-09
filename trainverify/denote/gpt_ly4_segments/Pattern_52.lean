/- Auto-generated pattern proof file.
   Pattern: 52
   Hash: 5dc4fe3a01d8cc6c
   Goals: 96
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_52_goalIds : List Nat := [96]
inductive pattern_52_target : Prop → Prop
  | goal_96 : pattern_52_target goal_96_stmt

def pattern_52_stmt : Prop :=
  ∀ {target : Prop}, pattern_52_target target → target
theorem prove_pattern_52 : pattern_52_stmt := by
  intro target h
  cases h with
  | goal_96 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_4
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

