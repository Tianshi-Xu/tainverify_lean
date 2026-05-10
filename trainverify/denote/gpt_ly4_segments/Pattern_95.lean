/- Auto-generated pattern proof file.
   Pattern: 95
   Hash: 5693f5d6954802d2
   Goals: 169
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_7

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_95_goalIds : List Nat := [169]
inductive pattern_95_target : Prop → Prop
  | goal_169 : pattern_95_target goal_169_stmt

def pattern_95_stmt : Prop :=
  ∀ {target : Prop}, pattern_95_target target → target
theorem prove_pattern_95 : pattern_95_stmt := by
  intro target h
  cases h with
  | goal_169 =>
      have hs := prove_segment_pattern_7 segment_pattern_7_target.inst_2
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

