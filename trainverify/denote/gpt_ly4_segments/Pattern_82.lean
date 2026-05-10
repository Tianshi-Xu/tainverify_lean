/- Auto-generated pattern proof file.
   Pattern: 82
   Hash: cedf711f29cb33ce
   Goals: 145, 171
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_82_goalIds : List Nat := [145, 171]
inductive pattern_82_target : Prop → Prop
  | goal_145 : pattern_82_target goal_145_stmt
  | goal_171 : pattern_82_target goal_171_stmt

def pattern_82_stmt : Prop :=
  ∀ {target : Prop}, pattern_82_target target → target
theorem prove_pattern_82 : pattern_82_stmt := by
  intro target h
  cases h with
  | goal_145 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_2
      exact hs.left
  | goal_171 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_2
      exact hs.right.right.left

end TrainVerify.Denote.GeneratedPatterns

