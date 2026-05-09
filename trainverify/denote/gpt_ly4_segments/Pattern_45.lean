/- Auto-generated pattern proof file.
   Pattern: 45
   Hash: e00b0161c106a61d
   Goals: 76, 78, 101, 103
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_45_goalIds : List Nat := [76, 78, 101, 103]
inductive pattern_45_target : Prop → Prop
  | goal_76 : pattern_45_target goal_76_stmt
  | goal_78 : pattern_45_target goal_78_stmt
  | goal_101 : pattern_45_target goal_101_stmt
  | goal_103 : pattern_45_target goal_103_stmt

def pattern_45_stmt : Prop :=
  ∀ {target : Prop}, pattern_45_target target → target
theorem prove_pattern_45 : pattern_45_stmt := by
  intro target h
  cases h with
  | goal_76 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_3
      exact hs.right.right.right.right.right.right.left
  | goal_78 => sorry
  | goal_101 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_4
      exact hs.right.right.right.right.right.right.left
  | goal_103 => sorry

end TrainVerify.Denote.GeneratedPatterns

