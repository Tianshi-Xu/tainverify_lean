/- Auto-generated pattern proof file.
   Pattern: 120
   Hash: 2a803104e732b46c
   Goals: 232
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_120_goalIds : List Nat := [232]
inductive pattern_120_target : Prop → Prop
  | goal_232 : pattern_120_target goal_232_stmt

def pattern_120_stmt : Prop :=
  ∀ {target : Prop}, pattern_120_target target → target
open TrainVerify.Denote.GeneratedSegmentPatterns

theorem prove_pattern_120 : pattern_120_stmt := by
  intro target h
  cases h with
  | goal_232 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_4
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

