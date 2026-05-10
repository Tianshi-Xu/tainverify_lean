/- Auto-generated pattern proof file.
   Pattern: 43
   Hash: 636e2544da31dfa4
   Goals: 73, 98
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_43_goalIds : List Nat := [73, 98]
inductive pattern_43_target : Prop → Prop
  | goal_73 : pattern_43_target goal_73_stmt
  | goal_98 : pattern_43_target goal_98_stmt

def pattern_43_stmt : Prop :=
  ∀ {target : Prop}, pattern_43_target target → target
theorem prove_pattern_43 : pattern_43_stmt := by
  intro target h
  cases h with
  | goal_73 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_3
      exact hs.right.right.right.left
  | goal_98 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_4
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

