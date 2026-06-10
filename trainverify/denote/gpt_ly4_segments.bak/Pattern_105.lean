/- Auto-generated pattern proof file.
   Pattern: 105
   Hash: dc9e058cbda65265
   Goals: 197
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_105_goalIds : List Nat := [197]
inductive pattern_105_target : Prop → Prop
  | goal_197 : pattern_105_target goal_197_stmt

def pattern_105_stmt : Prop :=
  ∀ {target : Prop}, pattern_105_target target → target
theorem prove_pattern_105 : pattern_105_stmt := by
  intro target h
  cases h with
  | goal_197 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_3
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

