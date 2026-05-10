/- Auto-generated pattern proof file.
   Pattern: 123
   Hash: 5fa001e9a332644f
   Goals: 236
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_123_goalIds : List Nat := [236]
inductive pattern_123_target : Prop → Prop
  | goal_236 : pattern_123_target goal_236_stmt

def pattern_123_stmt : Prop :=
  ∀ {target : Prop}, pattern_123_target target → target
theorem prove_pattern_123 : pattern_123_stmt := by
  intro target h
  cases h with
  | goal_236 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_4
      exact hs.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

