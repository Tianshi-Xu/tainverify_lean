/- Auto-generated pattern proof file.
   Pattern: 111
   Hash: fd13fb88f22bfeb3
   Goals: 205, 240
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_111_goalIds : List Nat := [205, 240]
inductive pattern_111_target : Prop → Prop
  | goal_205 : pattern_111_target goal_205_stmt
  | goal_240 : pattern_111_target goal_240_stmt

def pattern_111_stmt : Prop :=
  ∀ {target : Prop}, pattern_111_target target → target
theorem prove_pattern_111 : pattern_111_stmt := by
  intro target h
  cases h with
  | goal_205 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_3
      exact hs.right.left
  | goal_240 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_4
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

