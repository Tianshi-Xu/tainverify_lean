/- Auto-generated pattern proof file.
   Pattern: 88
   Hash: 822bcf4ecfb0936c
   Goals: 161
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_88_goalIds : List Nat := [161]
inductive pattern_88_target : Prop → Prop
  | goal_161 : pattern_88_target goal_161_stmt

def pattern_88_stmt : Prop :=
  ∀ {target : Prop}, pattern_88_target target → target
theorem prove_pattern_88 : pattern_88_stmt := by
  intro target h
  cases h with
  | goal_161 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_2
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

