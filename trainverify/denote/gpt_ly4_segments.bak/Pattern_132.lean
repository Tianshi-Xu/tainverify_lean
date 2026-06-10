/- Auto-generated pattern proof file.
   Pattern: 132
   Hash: 57c487c375656b24
   Goals: 266, 290, 292
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_132_goalIds : List Nat := [266, 290, 292]
inductive pattern_132_target : Prop → Prop
  | goal_266 : pattern_132_target goal_266_stmt
  | goal_290 : pattern_132_target goal_290_stmt
  | goal_292 : pattern_132_target goal_292_stmt

def pattern_132_stmt : Prop :=
  ∀ {target : Prop}, pattern_132_target target → target
theorem prove_pattern_132 : pattern_132_stmt := by
  intro target h
  cases h with
  | goal_266 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_1
      exact hs.right.left
  | goal_290 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_3
      exact hs.right.right.right.right.right.left
  | goal_292 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_3
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

