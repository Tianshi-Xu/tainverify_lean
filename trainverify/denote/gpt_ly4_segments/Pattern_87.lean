/- Auto-generated pattern proof file.
   Pattern: 87
   Hash: 170a42c41124a2b6
   Goals: 159
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_87_goalIds : List Nat := [159]
inductive pattern_87_target : Prop → Prop
  | goal_159 : pattern_87_target goal_159_stmt

def pattern_87_stmt : Prop :=
  ∀ {target : Prop}, pattern_87_target target → target
theorem prove_pattern_87 : pattern_87_stmt := by
  intro target h
  cases h with
  | goal_159 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_2
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

