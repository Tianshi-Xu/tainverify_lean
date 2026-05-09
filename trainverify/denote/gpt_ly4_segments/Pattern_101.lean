/- Auto-generated pattern proof file.
   Pattern: 101
   Hash: 12b7a7b4b39f41ac
   Goals: 184
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_101_goalIds : List Nat := [184]
inductive pattern_101_target : Prop → Prop
  | goal_184 : pattern_101_target goal_184_stmt

def pattern_101_stmt : Prop :=
  ∀ {target : Prop}, pattern_101_target target → target
theorem prove_pattern_101 : pattern_101_stmt := by
  intro target h
  cases h with
  | goal_184 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_3
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

