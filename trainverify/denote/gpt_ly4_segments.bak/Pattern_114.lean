/- Auto-generated pattern proof file.
   Pattern: 114
   Hash: 1b4403d68cc65102
   Goals: 211, 214, 246, 249
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7
import denote.gpt_ly4_segments.SegmentPattern_8

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_114_goalIds : List Nat := [211, 214, 246, 249]
inductive pattern_114_target : Prop → Prop
  | goal_211 : pattern_114_target goal_211_stmt
  | goal_214 : pattern_114_target goal_214_stmt
  | goal_246 : pattern_114_target goal_246_stmt
  | goal_249 : pattern_114_target goal_249_stmt

def pattern_114_stmt : Prop :=
  ∀ {target : Prop}, pattern_114_target target → target
theorem prove_pattern_114 : pattern_114_stmt := by
  intro target h
  cases h with
  | goal_211 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_3
      exact hs.right.right.right.right.right.right.right
  | goal_214 =>
      have hs := prove_segment_pattern_8 segment_pattern_8_target.inst_3
      exact hs.right.right
  | goal_246 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_4
      exact hs.right.right.right.right.right.right.right
  | goal_249 =>
      have hs := prove_segment_pattern_8 segment_pattern_8_target.inst_4
      exact hs.right.right

end TrainVerify.Denote.GeneratedPatterns

