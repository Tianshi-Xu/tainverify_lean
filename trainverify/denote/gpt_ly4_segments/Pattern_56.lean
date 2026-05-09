/- Auto-generated pattern proof file.
   Pattern: 56
   Hash: 4f4ca173921a3c96
   Goals: 110
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_56_goalIds : List Nat := [110]
inductive pattern_56_target : Prop → Prop
  | goal_110 : pattern_56_target goal_110_stmt

def pattern_56_stmt : Prop :=
  ∀ {target : Prop}, pattern_56_target target → target
theorem prove_pattern_56 : pattern_56_stmt := by
  intro target h
  cases h with
  | goal_110 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_1
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

