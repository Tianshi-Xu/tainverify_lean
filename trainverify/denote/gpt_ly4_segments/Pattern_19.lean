/- Auto-generated pattern proof file.
   Pattern: 19
   Hash: 079c368d91506bb2
   Goals: 23, 26, 51, 53, 106
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_19_goalIds : List Nat := [23, 26, 51, 53, 106]
inductive pattern_19_target : Prop → Prop
  | goal_23 : pattern_19_target goal_23_stmt
  | goal_26 : pattern_19_target goal_26_stmt
  | goal_51 : pattern_19_target goal_51_stmt
  | goal_53 : pattern_19_target goal_53_stmt
  | goal_106 : pattern_19_target goal_106_stmt

def pattern_19_stmt : Prop :=
  ∀ {target : Prop}, pattern_19_target target → target
theorem prove_pattern_19 : pattern_19_stmt := by
  intro target h
  cases h with
  | goal_23 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_1
      exact hs.right.right.right.left
  | goal_26 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_1
      exact hs.right.right.right.right.right.right.left
  | goal_51 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_2
      exact hs.right.right.right.right.right.right.left
  | goal_53 => sorry  -- not covered by any SegmentPattern (no segment sibling)
  | goal_106 => sorry  -- not covered by any SegmentPattern (no segment sibling)

end TrainVerify.Denote.GeneratedPatterns

