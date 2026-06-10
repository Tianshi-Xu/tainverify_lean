/- Auto-generated pattern proof file.
   Pattern: 36
   Hash: d11b1f63541a6fb6
   Goals: 54
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_1

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_36_goalIds : List Nat := [54]
inductive pattern_36_target : Prop → Prop
  | goal_54 : pattern_36_target goal_54_stmt

def pattern_36_stmt : Prop :=
  ∀ {target : Prop}, pattern_36_target target → target
theorem prove_pattern_36 : pattern_36_stmt := by
  intro target h
  cases h with
  | goal_54 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_3
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

