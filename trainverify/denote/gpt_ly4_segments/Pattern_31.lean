/- Auto-generated pattern proof file.
   Pattern: 31
   Hash: ffb9a4529bd4f852
   Goals: 44
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_31_goalIds : List Nat := [44]
inductive pattern_31_target : Prop → Prop
  | goal_44 : pattern_31_target goal_44_stmt

def pattern_31_stmt : Prop :=
  ∀ {target : Prop}, pattern_31_target target → target
theorem prove_pattern_31 : pattern_31_stmt := by
  intro target h
  cases h with
  | goal_44 =>
      have hs := TrainVerify.Denote.GeneratedSegmentPatterns.prove_segment_pattern_2
        TrainVerify.Denote.GeneratedSegmentPatterns.segment_pattern_2_target.inst_2
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

