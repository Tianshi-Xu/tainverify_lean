/- Auto-generated pattern proof file.
   Pattern: 81
   Hash: 167f5f740a7f0b4e
   Goals: 144
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_8

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_81_goalIds : List Nat := [144]
inductive pattern_81_target : Prop → Prop
  | goal_144 : pattern_81_target goal_144_stmt

def pattern_81_stmt : Prop :=
  ∀ {target : Prop}, pattern_81_target target → target
theorem prove_pattern_81 : pattern_81_stmt := by
  intro target h
  cases h with
  | goal_144 =>
      have hs := prove_segment_pattern_8 segment_pattern_8_target.inst_1
      exact hs.right.right

end TrainVerify.Denote.GeneratedPatterns

