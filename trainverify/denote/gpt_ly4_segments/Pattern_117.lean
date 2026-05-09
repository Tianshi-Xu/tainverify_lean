/- Auto-generated pattern proof file.
   Pattern: 117
   Hash: 5ee1d6a502ef74c1
   Goals: 227
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_5

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_117_goalIds : List Nat := [227]
inductive pattern_117_target : Prop → Prop
  | goal_227 : pattern_117_target goal_227_stmt

def pattern_117_stmt : Prop :=
  ∀ {target : Prop}, pattern_117_target target → target
theorem prove_pattern_117 : pattern_117_stmt := by
  intro target h
  cases h with
  | goal_227 =>
      have hs := prove_segment_pattern_5 segment_pattern_5_target.inst_4
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

