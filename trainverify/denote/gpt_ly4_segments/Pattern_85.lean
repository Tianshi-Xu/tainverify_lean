/- Auto-generated pattern proof file.
   Pattern: 85
   Hash: bb170cc2ef1a2985
   Goals: 156, 195, 230
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_85_goalIds : List Nat := [156, 195, 230]
inductive pattern_85_target : Prop → Prop
  | goal_156 : pattern_85_target goal_156_stmt
  | goal_195 : pattern_85_target goal_195_stmt
  | goal_230 : pattern_85_target goal_230_stmt

def pattern_85_stmt : Prop :=
  ∀ {target : Prop}, pattern_85_target target → target
theorem prove_pattern_85 : pattern_85_stmt := by
  intro target h
  cases h with
  | goal_156 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_2
      exact hs.right.right.right.left
  | goal_195 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_3
      exact hs.right.right.right.right.right.right.right
  | goal_230 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_4
      exact hs.right.right.right.right.right.right.right

end TrainVerify.Denote.GeneratedPatterns

