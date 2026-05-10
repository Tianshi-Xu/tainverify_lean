/- Auto-generated pattern proof file.
   Pattern: 134
   Hash: ffafe0f7e19884de
   Goals: 275, 303
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_134_goalIds : List Nat := [275, 303]
inductive pattern_134_target : Prop → Prop
  | goal_275 : pattern_134_target goal_275_stmt
  | goal_303 : pattern_134_target goal_303_stmt

def pattern_134_stmt : Prop :=
  ∀ {target : Prop}, pattern_134_target target → target
theorem prove_pattern_134 : pattern_134_stmt := by
  intro target h
  cases h with
  | goal_275 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_2
      exact hs.right.right.right.right.left
  | goal_303 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_4
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

