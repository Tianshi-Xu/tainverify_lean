/- Auto-generated pattern proof file.
   Pattern: 75
   Hash: d8751f17a8d75fdc
   Goals: 134
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_75_goalIds : List Nat := [134]
inductive pattern_75_target : Prop → Prop
  | goal_134 : pattern_75_target goal_134_stmt

def pattern_75_stmt : Prop :=
  ∀ {target : Prop}, pattern_75_target target → target
theorem prove_pattern_75 : pattern_75_stmt := by
  intro target h
  cases h with
  | goal_134 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_1
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

