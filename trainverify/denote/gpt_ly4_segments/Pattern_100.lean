/- Auto-generated pattern proof file.
   Pattern: 100
   Hash: 6535d8606ce7f24e
   Goals: 181, 207, 216, 242
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_100_goalIds : List Nat := [181, 207, 216, 242]
inductive pattern_100_target : Prop → Prop
  | goal_181 : pattern_100_target goal_181_stmt
  | goal_207 : pattern_100_target goal_207_stmt
  | goal_216 : pattern_100_target goal_216_stmt
  | goal_242 : pattern_100_target goal_242_stmt

def pattern_100_stmt : Prop :=
  ∀ {target : Prop}, pattern_100_target target → target
theorem prove_pattern_100 : pattern_100_stmt := by
  intro target h
  cases h with
  | goal_181 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_3
      exact hs.right.left
  | goal_207 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_3
      exact hs.right.right.right.left
  | goal_216 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_4
      exact hs.right.left
  | goal_242 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_4
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

