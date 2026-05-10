/- Auto-generated pattern proof file.
   Pattern: 80
   Hash: d139844ec7778cd9
   Goals: 143
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_8

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_80_goalIds : List Nat := [143]
inductive pattern_80_target : Prop → Prop
  | goal_143 : pattern_80_target goal_143_stmt

def pattern_80_stmt : Prop :=
  ∀ {target : Prop}, pattern_80_target target → target
theorem prove_pattern_80 : pattern_80_stmt := by
  intro target h
  cases h with
  | goal_143 =>
      have hs := prove_segment_pattern_8 segment_pattern_8_target.inst_1
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

