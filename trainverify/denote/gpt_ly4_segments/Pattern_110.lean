/- Auto-generated pattern proof file.
   Pattern: 110
   Hash: b932491bee1c0daf
   Goals: 204, 239
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_110_goalIds : List Nat := [204, 239]
inductive pattern_110_target : Prop → Prop
  | goal_204 : pattern_110_target goal_204_stmt
  | goal_239 : pattern_110_target goal_239_stmt

def pattern_110_stmt : Prop :=
  ∀ {target : Prop}, pattern_110_target target → target
theorem prove_pattern_110 : pattern_110_stmt := by
  intro target h
  cases h with
  | goal_204 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_3
      exact hs.left
  | goal_239 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_4
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

