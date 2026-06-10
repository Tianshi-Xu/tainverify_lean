/- Auto-generated pattern proof file.
   Pattern: 94
   Hash: b227dc374b18c4bb
   Goals: 167
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_94_goalIds : List Nat := [167]
inductive pattern_94_target : Prop → Prop
  | goal_167 : pattern_94_target goal_167_stmt

def pattern_94_stmt : Prop :=
  ∀ {target : Prop}, pattern_94_target target → target
theorem prove_pattern_94 : pattern_94_stmt := by
  intro target h
  cases h with
  | goal_167 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_2
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

