/- Auto-generated pattern proof file.
   Pattern: 44
   Hash: c118a3d5c38253d9
   Goals: 74, 79, 99, 104
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_1
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_44_goalIds : List Nat := [74, 79, 99, 104]
inductive pattern_44_target : Prop → Prop
  | goal_74 : pattern_44_target goal_74_stmt
  | goal_79 : pattern_44_target goal_79_stmt
  | goal_99 : pattern_44_target goal_99_stmt
  | goal_104 : pattern_44_target goal_104_stmt

def pattern_44_stmt : Prop :=
  ∀ {target : Prop}, pattern_44_target target → target
theorem prove_pattern_44 : pattern_44_stmt := by
  intro target h
  cases h with
  | goal_74 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_3
      exact hs.right.right.right.right.left
  | goal_79 =>
      have hs := prove_segment_pattern_1 segment_pattern_1_target.inst_4
      exact hs.left
  | goal_99 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_4
      exact hs.right.right.right.right.left
  | goal_104 => sorry

end TrainVerify.Denote.GeneratedPatterns

