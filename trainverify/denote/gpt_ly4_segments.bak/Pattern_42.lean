/- Auto-generated pattern proof file.
   Pattern: 42
   Hash: 71f8f15f7757f99e
   Goals: 71
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_42_goalIds : List Nat := [71]
inductive pattern_42_target : Prop → Prop
  | goal_71 : pattern_42_target goal_71_stmt

def pattern_42_stmt : Prop :=
  ∀ {target : Prop}, pattern_42_target target → target
theorem prove_pattern_42 : pattern_42_stmt := by
  intro target h
  cases h with
  | goal_71 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_3
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

