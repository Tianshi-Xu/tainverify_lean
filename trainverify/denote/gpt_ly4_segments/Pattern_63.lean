/- Auto-generated pattern proof file.
   Pattern: 63
   Hash: ae3c4abdfbe3fa40
   Goals: 119, 185, 187
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_63_goalIds : List Nat := [119, 185, 187]
inductive pattern_63_target : Prop → Prop
  | goal_119 : pattern_63_target goal_119_stmt
  | goal_185 : pattern_63_target goal_185_stmt
  | goal_187 : pattern_63_target goal_187_stmt

def pattern_63_stmt : Prop :=
  ∀ {target : Prop}, pattern_63_target target → target
theorem prove_pattern_63 : pattern_63_stmt := by
  intro target h
  cases h with
  | goal_119 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_1
      exact hs.right.left
  | goal_185 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_3
      exact hs.right.right.right.right.right.left
  | goal_187 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_3
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns
