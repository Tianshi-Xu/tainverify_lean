/- Auto-generated pattern proof file.
   Pattern: 38
   Hash: 219033270fed5ec2
   Goals: 66
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_38_goalIds : List Nat := [66]
inductive pattern_38_target : Prop → Prop
  | goal_66 : pattern_38_target goal_66_stmt

def pattern_38_stmt : Prop :=
  ∀ {target : Prop}, pattern_38_target target → target
theorem prove_pattern_38 : pattern_38_stmt := by
  intro target h
  cases h with
  | goal_66 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_3
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

