/- Auto-generated pattern proof file.
   Pattern: 107
   Hash: ff126a488ffa9918
   Goals: 200
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_107_goalIds : List Nat := [200]
inductive pattern_107_target : Prop → Prop
  | goal_200 : pattern_107_target goal_200_stmt

def pattern_107_stmt : Prop :=
  ∀ {target : Prop}, pattern_107_target target → target
theorem prove_pattern_107 : pattern_107_stmt := by
  intro target h
  cases h with
  | goal_200 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_3
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

