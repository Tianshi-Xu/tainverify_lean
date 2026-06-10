/- Auto-generated pattern proof file.
   Pattern: 119
   Hash: 2c3a77c412c5caa9
   Goals: 231
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_119_goalIds : List Nat := [231]
inductive pattern_119_target : Prop → Prop
  | goal_231 : pattern_119_target goal_231_stmt

def pattern_119_stmt : Prop :=
  ∀ {target : Prop}, pattern_119_target target → target
theorem prove_pattern_119 : pattern_119_stmt := by
  intro target h
  cases h with
  | goal_231 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_4
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

