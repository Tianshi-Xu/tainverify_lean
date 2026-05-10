/- Auto-generated pattern proof file.
   Pattern: 41
   Hash: cdd25357f2008c40
   Goals: 70
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_41_goalIds : List Nat := [70]
inductive pattern_41_target : Prop → Prop
  | goal_70 : pattern_41_target goal_70_stmt

def pattern_41_stmt : Prop :=
  ∀ {target : Prop}, pattern_41_target target → target
theorem prove_pattern_41 : pattern_41_stmt := by
  intro target h
  cases h with
  | goal_70 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_3
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

