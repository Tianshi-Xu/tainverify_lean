/- Auto-generated pattern proof file.
   Pattern: 13
   Hash: 8b010ba891fb5a35
   Goals: 17
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_13_goalIds : List Nat := [17]
inductive pattern_13_target : Prop → Prop
  | goal_17 : pattern_13_target goal_17_stmt

def pattern_13_stmt : Prop :=
  ∀ {target : Prop}, pattern_13_target target → target
theorem prove_pattern_13 : pattern_13_stmt := by
  intro target h
  cases h with
  | goal_17 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_1
      exact hs.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

