/- Auto-generated pattern proof file.
   Pattern: 79
   Hash: 6522a801ae6873b5
   Goals: 142
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_8

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_79_goalIds : List Nat := [142]
inductive pattern_79_target : Prop → Prop
  | goal_142 : pattern_79_target goal_142_stmt

def pattern_79_stmt : Prop :=
  ∀ {target : Prop}, pattern_79_target target → target
theorem prove_pattern_79 : pattern_79_stmt := by
  intro target h
  cases h with
  | goal_142 =>
      have hs := prove_segment_pattern_8 segment_pattern_8_target.inst_1
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

