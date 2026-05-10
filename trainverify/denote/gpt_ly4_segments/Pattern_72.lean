/- Auto-generated pattern proof file.
   Pattern: 72
   Hash: 60b2b79ebfc5c86d
   Goals: 131
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_72_goalIds : List Nat := [131]
inductive pattern_72_target : Prop → Prop
  | goal_131 : pattern_72_target goal_131_stmt

def pattern_72_stmt : Prop :=
  ∀ {target : Prop}, pattern_72_target target → target
theorem prove_pattern_72 : pattern_72_stmt := by
  intro target h
  cases h with
  | goal_131 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_1
      exact hs.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

