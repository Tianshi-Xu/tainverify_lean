/- Auto-generated pattern proof file.
   Pattern: 12
   Hash: b7d5e9d14bd05b5a
   Goals: 16
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_12_goalIds : List Nat := [16]
inductive pattern_12_target : Prop → Prop
  | goal_16 : pattern_12_target goal_16_stmt

def pattern_12_stmt : Prop :=
  ∀ {target : Prop}, pattern_12_target target → target
theorem prove_pattern_12 : pattern_12_stmt := by
  intro target h
  cases h with
  | goal_16 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_1
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

