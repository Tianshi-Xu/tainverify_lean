/- Auto-generated pattern proof file.
   Pattern: 37
   Hash: e5d4d61eeb799187
   Goals: 65
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_37_goalIds : List Nat := [65]
inductive pattern_37_target : Prop → Prop
  | goal_65 : pattern_37_target goal_65_stmt

def pattern_37_stmt : Prop :=
  ∀ {target : Prop}, pattern_37_target target → target
theorem prove_pattern_37 : pattern_37_stmt := by
  intro target h
  cases h with
  | goal_65 =>
      have hs := prove_segment_pattern_2 segment_pattern_2_target.inst_3
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

