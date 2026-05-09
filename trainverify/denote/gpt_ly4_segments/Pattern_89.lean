/- Auto-generated pattern proof file.
   Pattern: 89
   Hash: fe11c89e05945b6a
   Goals: 162
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_89_goalIds : List Nat := [162]
inductive pattern_89_target : Prop → Prop
  | goal_162 : pattern_89_target goal_162_stmt

def pattern_89_stmt : Prop :=
  ∀ {target : Prop}, pattern_89_target target → target
theorem prove_pattern_89 : pattern_89_stmt := by
  intro target h
  cases h with
  | goal_162 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_2
      exact hs.right.left

end TrainVerify.Denote.GeneratedPatterns

