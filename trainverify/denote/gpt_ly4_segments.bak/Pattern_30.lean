/- Auto-generated pattern proof file.
   Pattern: 30
   Hash: 21a76ff14018e094
   Goals: 43, 68
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_30_goalIds : List Nat := [43, 68]
inductive pattern_30_target : Prop → Prop
  | goal_43 : pattern_30_target goal_43_stmt
  | goal_68 : pattern_30_target goal_68_stmt

def pattern_30_stmt : Prop :=
  ∀ {target : Prop}, pattern_30_target target → target
theorem prove_pattern_30 : pattern_30_stmt := by
  intro target h
  cases h with
  | goal_43 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_2
      exact hs.right.right.right.right.right.right.left
  | goal_68 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_3
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

