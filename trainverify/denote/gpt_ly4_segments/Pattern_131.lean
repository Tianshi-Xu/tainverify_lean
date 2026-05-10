/- Auto-generated pattern proof file.
   Pattern: 131
   Hash: cd4c1af3aff22a92
   Goals: 265
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_10

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_131_goalIds : List Nat := [265]
inductive pattern_131_target : Prop → Prop
  | goal_265 : pattern_131_target goal_265_stmt

def pattern_131_stmt : Prop :=
  ∀ {target : Prop}, pattern_131_target target → target

theorem prove_pattern_131 : pattern_131_stmt := by
  intro target h
  cases h
  have hs := prove_segment_pattern_10 segment_pattern_10_target.inst_1
  exact hs.left

end TrainVerify.Denote.GeneratedPatterns

