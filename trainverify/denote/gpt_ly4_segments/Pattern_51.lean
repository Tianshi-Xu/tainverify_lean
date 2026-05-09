/- Auto-generated pattern proof file.
   Pattern: 51
   Hash: 4312b7357cfe03bd
   Goals: 95
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_51_goalIds : List Nat := [95]
inductive pattern_51_target : Prop → Prop
  | goal_95 : pattern_51_target goal_95_stmt

def pattern_51_stmt : Prop :=
  ∀ {target : Prop}, pattern_51_target target → target
theorem prove_pattern_51 : pattern_51_stmt := by
  intro target h
  cases h with
  | goal_95 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_4
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

