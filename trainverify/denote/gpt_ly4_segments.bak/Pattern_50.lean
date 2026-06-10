/- Auto-generated pattern proof file.
   Pattern: 50
   Hash: 7b2190bf8a3838fe
   Goals: 94
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_50_goalIds : List Nat := [94]
inductive pattern_50_target : Prop → Prop
  | goal_94 : pattern_50_target goal_94_stmt

def pattern_50_stmt : Prop :=
  ∀ {target : Prop}, pattern_50_target target → target
theorem prove_pattern_50 : pattern_50_stmt := by
  intro target h
  cases h with
  | goal_94 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_4
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

