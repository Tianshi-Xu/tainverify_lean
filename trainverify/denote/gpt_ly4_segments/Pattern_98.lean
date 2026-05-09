/- Auto-generated pattern proof file.
   Pattern: 98
   Hash: 351a6e0e58da6703
   Goals: 177
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_8

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_98_goalIds : List Nat := [177]
inductive pattern_98_target : Prop → Prop
  | goal_177 : pattern_98_target goal_177_stmt

def pattern_98_stmt : Prop :=
  ∀ {target : Prop}, pattern_98_target target → target
theorem prove_pattern_98 : pattern_98_stmt := by
  intro target h
  cases h with
  | goal_177 =>
      have hs := prove_segment_pattern_8 segment_pattern_8_target.inst_2
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

