/- Auto-generated pattern proof file.
   Pattern: 61
   Hash: 311c9abadc02f73b
   Goals: 115, 117, 152, 189, 224
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_61_goalIds : List Nat := [115, 117, 152, 189, 224]
inductive pattern_61_target : Prop → Prop
  | goal_115 : pattern_61_target goal_115_stmt
  | goal_117 : pattern_61_target goal_117_stmt
  | goal_152 : pattern_61_target goal_152_stmt
  | goal_189 : pattern_61_target goal_189_stmt
  | goal_224 : pattern_61_target goal_224_stmt

def pattern_61_stmt : Prop :=
  ∀ {target : Prop}, pattern_61_target target → target
theorem prove_pattern_61 : pattern_61_stmt := by
  intro target h
  cases h with
  | goal_115 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_1
      exact hs.right.right.right.right.right.left
  | goal_117 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_1
      exact hs.right.right.right.right.right.right.right
  | goal_152 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_2
      exact hs.right.right.right.right.right.right.right
  | goal_189 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_3
      exact hs.right.left
  | goal_224 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_4
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

