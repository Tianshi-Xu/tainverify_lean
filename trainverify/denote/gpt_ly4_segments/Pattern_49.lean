/- Auto-generated pattern proof file.
   Pattern: 49
   Hash: 9bd201aef66ba58a
   Goals: 93
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_49_goalIds : List Nat := [93]
inductive pattern_49_target : Prop → Prop
  | goal_93 : pattern_49_target goal_93_stmt

def pattern_49_stmt : Prop :=
  ∀ {target : Prop}, pattern_49_target target → target
theorem prove_pattern_49 : pattern_49_stmt := by
  intro target h
  cases h with
  | goal_93 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_4
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

