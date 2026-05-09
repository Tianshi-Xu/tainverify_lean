/- Auto-generated pattern proof file.
   Pattern: 70
   Hash: 4fc09d1555501129
   Goals: 129
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_70_goalIds : List Nat := [129]
inductive pattern_70_target : Prop → Prop
  | goal_129 : pattern_70_target goal_129_stmt

def pattern_70_stmt : Prop :=
  ∀ {target : Prop}, pattern_70_target target → target
theorem prove_pattern_70 : pattern_70_stmt := by
  intro target h
  cases h with
  | goal_129 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_1
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

