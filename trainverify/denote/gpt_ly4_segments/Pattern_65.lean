/- Auto-generated pattern proof file.
   Pattern: 65
   Hash: 3b0c900681d51648
   Goals: 122, 127
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_65_goalIds : List Nat := [122, 127]
inductive pattern_65_target : Prop → Prop
  | goal_122 : pattern_65_target goal_122_stmt
  | goal_127 : pattern_65_target goal_127_stmt

def pattern_65_stmt : Prop :=
  ∀ {target : Prop}, pattern_65_target target → target
theorem prove_pattern_65 : pattern_65_stmt := by
  intro target h
  cases h with
  | goal_122 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_1
      exact hs.right.right.right.right.left
  | goal_127 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_1
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

