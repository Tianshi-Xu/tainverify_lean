/- Auto-generated pattern proof file.
   Pattern: 99
   Hash: d94396f9bc6e75cf
   Goals: 180
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_4

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_99_goalIds : List Nat := [180]
inductive pattern_99_target : Prop → Prop
  | goal_180 : pattern_99_target goal_180_stmt

def pattern_99_stmt : Prop :=
  ∀ {target : Prop}, pattern_99_target target → target
theorem prove_pattern_99 : pattern_99_stmt := by
  intro target h
  cases h with
  | goal_180 =>
      have hs := prove_segment_pattern_4 segment_pattern_4_target.inst_3
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

