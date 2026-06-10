/- Auto-generated pattern proof file.
   Pattern: 67
   Hash: cbb8aacd58872724
   Goals: 124
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_67_goalIds : List Nat := [124]
inductive pattern_67_target : Prop → Prop
  | goal_124 : pattern_67_target goal_124_stmt

def pattern_67_stmt : Prop :=
  ∀ {target : Prop}, pattern_67_target target → target
theorem prove_pattern_67 : pattern_67_stmt := by
  intro target h
  cases h with
  | goal_124 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_1
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

