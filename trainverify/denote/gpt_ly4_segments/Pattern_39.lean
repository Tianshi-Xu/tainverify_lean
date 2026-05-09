/- Auto-generated pattern proof file.
   Pattern: 39
   Hash: 06efedb9860cad7c
   Goals: 67
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_39_goalIds : List Nat := [67]
inductive pattern_39_target : Prop → Prop
  | goal_67 : pattern_39_target goal_67_stmt

def pattern_39_stmt : Prop :=
  ∀ {target : Prop}, pattern_39_target target → target
theorem prove_pattern_39 : pattern_39_stmt := by
  intro target h
  cases h with
  | goal_67 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_3
      exact hs.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

