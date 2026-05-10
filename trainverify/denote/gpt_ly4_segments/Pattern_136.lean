/- Auto-generated pattern proof file.
   Pattern: 136
   Hash: 03d3dfbf604868f7
   Goals: 283
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_136_goalIds : List Nat := [283]
inductive pattern_136_target : Prop → Prop
  | goal_283 : pattern_136_target goal_283_stmt

def pattern_136_stmt : Prop :=
  ∀ {target : Prop}, pattern_136_target target → target
theorem prove_pattern_136 : pattern_136_stmt := by
  intro target h
  cases h with
  | goal_283 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_2
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

