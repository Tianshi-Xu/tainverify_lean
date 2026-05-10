/- Auto-generated pattern proof file.
   Pattern: 91
   Hash: d2e2a2bd15b78ef5
   Goals: 164, 199
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_91_goalIds : List Nat := [164, 199]
inductive pattern_91_target : Prop → Prop
  | goal_164 : pattern_91_target goal_164_stmt
  | goal_199 : pattern_91_target goal_199_stmt

def pattern_91_stmt : Prop :=
  ∀ {target : Prop}, pattern_91_target target → target
theorem prove_pattern_91 : pattern_91_stmt := by
  intro target h
  cases h with
  | goal_164 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_2
      exact hs.right.right.right.left
  | goal_199 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_3
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

