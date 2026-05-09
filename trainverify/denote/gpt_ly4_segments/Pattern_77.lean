/- Auto-generated pattern proof file.
   Pattern: 77
   Hash: f376f24d00c25d0f
   Goals: 136, 260
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7
import denote.gpt_ly4_segments.SegmentPattern_9

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_77_goalIds : List Nat := [136, 260]
inductive pattern_77_target : Prop → Prop
  | goal_136 : pattern_77_target goal_136_stmt
  | goal_260 : pattern_77_target goal_260_stmt

def pattern_77_stmt : Prop :=
  ∀ {target : Prop}, pattern_77_target target → target
theorem prove_pattern_77 : pattern_77_stmt := by
  intro target h
  cases h with
  | goal_136 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_1
      exact hs.right.right.left
  | goal_260 =>
      have hs := prove_segment_pattern_9 segment_pattern_9_target.inst_1
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

