/- Auto-generated pattern proof file.
   Pattern: 121
   Hash: 4581aeda3eb6fab4
   Goals: 234
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_121_goalIds : List Nat := [234]
inductive pattern_121_target : Prop → Prop
  | goal_234 : pattern_121_target goal_234_stmt

def pattern_121_stmt : Prop :=
  ∀ {target : Prop}, pattern_121_target target → target
theorem prove_pattern_121 : pattern_121_stmt := by
  intro target h
  cases h with
  | goal_234 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_4
      exact hs.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

