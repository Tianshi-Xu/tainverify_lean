/- Auto-generated pattern proof file.
   Pattern: 64
   Hash: 25b31a4fd13f0085
   Goals: 121, 125, 160, 193, 228
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_64_goalIds : List Nat := [121, 125, 160, 193, 228]
inductive pattern_64_target : Prop → Prop
  | goal_121 : pattern_64_target goal_121_stmt
  | goal_125 : pattern_64_target goal_125_stmt
  | goal_160 : pattern_64_target goal_160_stmt
  | goal_193 : pattern_64_target goal_193_stmt
  | goal_228 : pattern_64_target goal_228_stmt

def pattern_64_stmt : Prop :=
  ∀ {target : Prop}, pattern_64_target target → target
theorem prove_pattern_64 : pattern_64_stmt := by
  intro target h
  cases h with
  | goal_121 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_1
      exact hs.right.right.right.left
  | goal_125 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_1
      exact hs.right.right.right.right.right.right.right
  | goal_160 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_2
      exact hs.right.right.right.right.right.right.right
  | goal_193 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_3
      exact hs.right.right.right.right.right.left
  | goal_228 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_4
      exact hs.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

