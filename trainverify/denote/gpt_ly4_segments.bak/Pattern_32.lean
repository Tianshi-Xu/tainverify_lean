/- Auto-generated pattern proof file.
   Pattern: 32
   Hash: 34b81de260e2aada
   Goals: 45
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_32_goalIds : List Nat := [45]
inductive pattern_32_target : Prop → Prop
  | goal_45 : pattern_32_target goal_45_stmt

def pattern_32_stmt : Prop :=
  ∀ {target : Prop}, pattern_32_target target → target
theorem prove_pattern_32 : pattern_32_stmt := by
  intro target h
  cases h with
  | goal_45 =>
      have hs := prove_segment_pattern_3 segment_pattern_3_target.inst_2
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

