/- Auto-generated pattern proof file.
   Pattern: 35
   Hash: 8e83bc5d9a30ac61
   Goals: 52
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_35_goalIds : List Nat := [52]
inductive pattern_35_target : Prop → Prop
  | goal_52 : pattern_35_target goal_52_stmt

def pattern_35_stmt : Prop :=
  ∀ {target : Prop}, pattern_35_target target → target
theorem prove_pattern_35 : pattern_35_stmt := by
  intro target h
  cases h with
  | goal_52 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_2
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

