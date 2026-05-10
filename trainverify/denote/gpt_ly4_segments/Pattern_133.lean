/- Auto-generated pattern proof file.
   Pattern: 133
   Hash: 574af4a3647d8990
   Goals: 270, 274
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_133_goalIds : List Nat := [270, 274]
inductive pattern_133_target : Prop → Prop
  | goal_270 : pattern_133_target goal_270_stmt
  | goal_274 : pattern_133_target goal_274_stmt

def pattern_133_stmt : Prop :=
  ∀ {target : Prop}, pattern_133_target target → target
theorem prove_pattern_133 : pattern_133_stmt := by
  intro target h
  cases h with
  | goal_270 =>
      have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_1
      exact hs.right.right.right.right.right
  | goal_274 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_2
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

