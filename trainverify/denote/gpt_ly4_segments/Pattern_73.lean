/- Auto-generated pattern proof file.
   Pattern: 73
   Hash: 367f4838cb70de53
   Goals: 132
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_73_goalIds : List Nat := [132]
inductive pattern_73_target : Prop → Prop
  | goal_132 : pattern_73_target goal_132_stmt

def pattern_73_stmt : Prop :=
  ∀ {target : Prop}, pattern_73_target target → target
theorem prove_pattern_73 : pattern_73_stmt := by
  intro target h
  cases h with
  | goal_132 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_1
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

