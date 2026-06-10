/- Auto-generated pattern proof file.
   Pattern: 83
   Hash: 7e437332db8ccdb6
   Goals: 149
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_83_goalIds : List Nat := [149]
inductive pattern_83_target : Prop → Prop
  | goal_149 : pattern_83_target goal_149_stmt

def pattern_83_stmt : Prop :=
  ∀ {target : Prop}, pattern_83_target target → target
theorem prove_pattern_83 : pattern_83_stmt := by
  intro target h
  cases h with
  | goal_149 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_2
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

