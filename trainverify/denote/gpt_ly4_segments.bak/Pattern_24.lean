/- Auto-generated pattern proof file.
   Pattern: 24
   Hash: 362fe28a330ba7b8
   Goals: 29, 49
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_1
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_24_goalIds : List Nat := [29, 49]
inductive pattern_24_target : Prop → Prop
  | goal_29 : pattern_24_target goal_29_stmt
  | goal_49 : pattern_24_target goal_49_stmt

def pattern_24_stmt : Prop :=
  ∀ {target : Prop}, pattern_24_target target → target
theorem prove_pattern_24 : pattern_24_stmt := by
  intro target h
  cases h with
  | goal_29 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_2
      exact hs.left
  | goal_49 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_2
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

