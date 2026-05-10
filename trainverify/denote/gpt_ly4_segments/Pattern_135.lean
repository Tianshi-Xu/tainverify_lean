/- Auto-generated pattern proof file.
   Pattern: 135
   Hash: aed5adffc490ef93
   Goals: 279
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_135_goalIds : List Nat := [279]
inductive pattern_135_target : Prop → Prop
  | goal_279 : pattern_135_target goal_279_stmt

def pattern_135_stmt : Prop :=
  ∀ {target : Prop}, pattern_135_target target → target
theorem prove_pattern_135 : pattern_135_stmt := by
  intro target h
  cases h with
  | goal_279 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_2
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

