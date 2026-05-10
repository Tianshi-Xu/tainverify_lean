/- Auto-generated pattern proof file.
   Pattern: 97
   Hash: efee555c383bc1be
   Goals: 172
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_97_goalIds : List Nat := [172]
inductive pattern_97_target : Prop → Prop
  | goal_172 : pattern_97_target goal_172_stmt

def pattern_97_stmt : Prop :=
  ∀ {target : Prop}, pattern_97_target target → target
theorem prove_pattern_97 : pattern_97_stmt := by
  intro target h
  cases h with
  | goal_172 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_2
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

