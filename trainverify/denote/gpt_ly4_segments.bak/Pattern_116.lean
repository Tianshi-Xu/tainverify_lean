/- Auto-generated pattern proof file.
   Pattern: 116
   Hash: e6181364fcbf9b02
   Goals: 219
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_116_goalIds : List Nat := [219]
inductive pattern_116_target : Prop → Prop
  | goal_219 : pattern_116_target goal_219_stmt

def pattern_116_stmt : Prop :=
  ∀ {target : Prop}, pattern_116_target target → target
theorem prove_pattern_116 : pattern_116_stmt := by
  intro target h
  cases h with
  | goal_219 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_4
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

