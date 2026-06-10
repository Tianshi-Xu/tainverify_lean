/- Auto-generated pattern proof file.
   Pattern: 141
   Hash: 937a885642ea4bfc
   Goals: 305
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_141_goalIds : List Nat := [305]
inductive pattern_141_target : Prop → Prop
  | goal_305 : pattern_141_target goal_305_stmt

def pattern_141_stmt : Prop :=
  ∀ {target : Prop}, pattern_141_target target → target
theorem prove_pattern_141 : pattern_141_stmt := by
  intro target h
  cases h with
  | goal_305 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_4
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

