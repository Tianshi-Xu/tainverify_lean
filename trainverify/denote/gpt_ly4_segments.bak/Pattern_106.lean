/- Auto-generated pattern proof file.
   Pattern: 106
   Hash: ca845ebaeae424c9
   Goals: 198
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_106_goalIds : List Nat := [198]
inductive pattern_106_target : Prop → Prop
  | goal_198 : pattern_106_target goal_198_stmt

def pattern_106_stmt : Prop :=
  ∀ {target : Prop}, pattern_106_target target → target
theorem prove_pattern_106 : pattern_106_stmt := by
  intro target h
  cases h with
  | goal_198 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_3
      exact hs.right.right.left

end TrainVerify.Denote.GeneratedPatterns

