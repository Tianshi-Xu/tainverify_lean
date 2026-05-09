/- Auto-generated pattern proof file.
   Pattern: 86
   Hash: 3ace81adb4a0f428
   Goals: 157
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_86_goalIds : List Nat := [157]
inductive pattern_86_target : Prop → Prop
  | goal_157 : pattern_86_target goal_157_stmt

def pattern_86_stmt : Prop :=
  ∀ {target : Prop}, pattern_86_target target → target
theorem prove_pattern_86 : pattern_86_stmt := by
  intro target h
  cases h with
  | goal_157 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_2
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

