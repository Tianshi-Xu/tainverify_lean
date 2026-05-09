/- Auto-generated pattern proof file.
   Pattern: 109
   Hash: 392d014c0fc2b2c0
   Goals: 202
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_109_goalIds : List Nat := [202]
inductive pattern_109_target : Prop → Prop
  | goal_202 : pattern_109_target goal_202_stmt

def pattern_109_stmt : Prop :=
  ∀ {target : Prop}, pattern_109_target target → target
theorem prove_pattern_109 : pattern_109_stmt := by
  intro target h
  cases h with
  | goal_202 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_3
      exact hs.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

