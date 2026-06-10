/- Auto-generated pattern proof file.
   Pattern: 96
   Hash: 566a03d6acd2c3a2
   Goals: 170
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_96_goalIds : List Nat := [170]
inductive pattern_96_target : Prop → Prop
  | goal_170 : pattern_96_target goal_170_stmt

def pattern_96_stmt : Prop :=
  ∀ {target : Prop}, pattern_96_target target → target
theorem prove_pattern_96 : pattern_96_stmt := by
  intro target h
  cases h with
  | goal_170 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_2
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

