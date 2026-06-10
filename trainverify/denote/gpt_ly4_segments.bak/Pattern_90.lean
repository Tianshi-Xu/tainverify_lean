/- Auto-generated pattern proof file.
   Pattern: 90
   Hash: 1ab8d618cf3be72d
   Goals: 163, 233
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_90_goalIds : List Nat := [163, 233]
inductive pattern_90_target : Prop → Prop
  | goal_163 : pattern_90_target goal_163_stmt
  | goal_233 : pattern_90_target goal_233_stmt

def pattern_90_stmt : Prop :=
  ∀ {target : Prop}, pattern_90_target target → target
theorem prove_pattern_90 : pattern_90_stmt := by
  intro target h
  cases h with
  | goal_163 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_2
      exact hs.right.right.left
  | goal_233 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_4
      exact hs.right.right.left

end TrainVerify.Denote.GeneratedPatterns

