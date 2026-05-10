/- Auto-generated pattern proof file.
   Pattern: 60
   Hash: 4e07ca3b913e473b
   Goals: 114
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_60_goalIds : List Nat := [114]
inductive pattern_60_target : Prop → Prop
  | goal_114 : pattern_60_target goal_114_stmt

def pattern_60_stmt : Prop :=
  ∀ {target : Prop}, pattern_60_target target → target
theorem prove_pattern_60 : pattern_60_stmt := by
  intro target h
  cases h with
  | goal_114 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_1
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

