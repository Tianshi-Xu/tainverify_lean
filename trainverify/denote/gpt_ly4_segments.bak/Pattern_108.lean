/- Auto-generated pattern proof file.
   Pattern: 108
   Hash: 22d7a4b25021c9d1
   Goals: 201
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_108_goalIds : List Nat := [201]
inductive pattern_108_target : Prop → Prop
  | goal_201 : pattern_108_target goal_201_stmt

def pattern_108_stmt : Prop :=
  ∀ {target : Prop}, pattern_108_target target → target
theorem prove_pattern_108 : pattern_108_stmt := by
  intro target h
  cases h with
  | goal_201 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_3
      exact hs.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

