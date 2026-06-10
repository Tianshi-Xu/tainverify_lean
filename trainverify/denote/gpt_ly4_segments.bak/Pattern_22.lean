/- Auto-generated pattern proof file.
   Pattern: 22
   Hash: 0565fea697fd9ce8
   Goals: 27
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_22_goalIds : List Nat := [27]
inductive pattern_22_target : Prop → Prop
  | goal_27 : pattern_22_target goal_27_stmt

def pattern_22_stmt : Prop :=
  ∀ {target : Prop}, pattern_22_target target → target
theorem prove_pattern_22 : pattern_22_stmt := by
  intro target h
  cases h with
  | goal_27 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_1
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

