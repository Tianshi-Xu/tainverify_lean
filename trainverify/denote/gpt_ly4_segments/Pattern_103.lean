/- Auto-generated pattern proof file.
   Pattern: 103
   Hash: b87872210a5737be
   Goals: 194
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_103_goalIds : List Nat := [194]
inductive pattern_103_target : Prop → Prop
  | goal_194 : pattern_103_target goal_194_stmt

def pattern_103_stmt : Prop :=
  ∀ {target : Prop}, pattern_103_target target → target
theorem prove_pattern_103 : pattern_103_stmt := by
  intro target h
  cases h with
  | goal_194 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_3
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

