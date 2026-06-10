/- Auto-generated pattern proof file.
   Pattern: 20
   Hash: 6413053af5c9da02
   Goals: 24
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_20_goalIds : List Nat := [24]
inductive pattern_20_target : Prop → Prop
  | goal_24 : pattern_20_target goal_24_stmt

def pattern_20_stmt : Prop :=
  ∀ {target : Prop}, pattern_20_target target → target
theorem prove_pattern_20 : pattern_20_stmt := by
  intro target h
  cases h with
  | goal_24 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_1
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

