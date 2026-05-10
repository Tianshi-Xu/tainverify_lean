/- Auto-generated pattern proof file.
   Pattern: 92
   Hash: 16c7c037822ff585
   Goals: 165
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_92_goalIds : List Nat := [165]
inductive pattern_92_target : Prop → Prop
  | goal_165 : pattern_92_target goal_165_stmt

def pattern_92_stmt : Prop :=
  ∀ {target : Prop}, pattern_92_target target → target
theorem prove_pattern_92 : pattern_92_stmt := by
  intro target h
  cases h with
  | goal_165 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_2
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

