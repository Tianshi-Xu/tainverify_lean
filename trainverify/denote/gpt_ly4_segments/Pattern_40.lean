/- Auto-generated pattern proof file.
   Pattern: 40
   Hash: 67ee92c22bc36ee0
   Goals: 69
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_40_goalIds : List Nat := [69]
inductive pattern_40_target : Prop → Prop
  | goal_69 : pattern_40_target goal_69_stmt

def pattern_40_stmt : Prop :=
  ∀ {target : Prop}, pattern_40_target target → target
theorem prove_pattern_40 : pattern_40_stmt := by
  intro target h
  cases h with
  | goal_69 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_3
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

