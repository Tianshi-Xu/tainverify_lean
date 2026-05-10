/- Auto-generated pattern proof file.
   Pattern: 118
   Hash: b6e95f2ab8c37f12
   Goals: 229
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_118_goalIds : List Nat := [229]
inductive pattern_118_target : Prop → Prop
  | goal_229 : pattern_118_target goal_229_stmt

def pattern_118_stmt : Prop :=
  ∀ {target : Prop}, pattern_118_target target → target
theorem prove_pattern_118 : pattern_118_stmt := by
  intro target h
  cases h with
  | goal_229 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_4
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

