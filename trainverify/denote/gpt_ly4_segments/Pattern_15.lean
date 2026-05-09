/- Auto-generated pattern proof file.
   Pattern: 15
   Hash: e5e3b810aabecab2
   Goals: 19
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_15_goalIds : List Nat := [19]
inductive pattern_15_target : Prop → Prop
  | goal_19 : pattern_15_target goal_19_stmt

def pattern_15_stmt : Prop :=
  ∀ {target : Prop}, pattern_15_target target → target
theorem prove_pattern_15 : pattern_15_stmt := by
  intro target h
  cases h with
  | goal_19 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_1
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

