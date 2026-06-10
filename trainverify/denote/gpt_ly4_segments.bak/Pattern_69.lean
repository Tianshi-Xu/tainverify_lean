/- Auto-generated pattern proof file.
   Pattern: 69
   Hash: 370886e526256ef8
   Goals: 128
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_69_goalIds : List Nat := [128]
inductive pattern_69_target : Prop → Prop
  | goal_128 : pattern_69_target goal_128_stmt

def pattern_69_stmt : Prop :=
  ∀ {target : Prop}, pattern_69_target target → target
theorem prove_pattern_69 : pattern_69_stmt := by
  intro target h
  cases h with
  | goal_128 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_1
      exact hs.right.right.left

end TrainVerify.Denote.GeneratedPatterns

