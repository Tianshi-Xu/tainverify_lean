/- Auto-generated pattern proof file.
   Pattern: 127
   Hash: e225aa80702b3daa
   Goals: 257, 267, 271, 281
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_127_goalIds : List Nat := [257, 267, 271, 281]
inductive pattern_127_target : Prop → Prop
  | goal_257 : pattern_127_target goal_257_stmt
  | goal_267 : pattern_127_target goal_267_stmt
  | goal_271 : pattern_127_target goal_271_stmt
  | goal_281 : pattern_127_target goal_281_stmt

def pattern_127_stmt : Prop :=
  ∀ {target : Prop}, pattern_127_target target → target

theorem prove_pattern_127 : pattern_127_stmt := by
  intro target h
  cases h with
  | goal_257 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_1
      exact hs.left
  | goal_267 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_1
      exact hs.right.right.left
  | goal_271 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_2
      exact hs.left
  | goal_281 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_2
      exact hs.right.right.left

end TrainVerify.Denote.GeneratedPatterns
