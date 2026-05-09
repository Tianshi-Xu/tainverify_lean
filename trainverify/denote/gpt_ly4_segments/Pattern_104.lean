/- Auto-generated pattern proof file.
   Pattern: 104
   Hash: 6fe5909eca745485
   Goals: 196
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_104_goalIds : List Nat := [196]
inductive pattern_104_target : Prop → Prop
  | goal_196 : pattern_104_target goal_196_stmt

def pattern_104_stmt : Prop :=
  ∀ {target : Prop}, pattern_104_target target → target
theorem prove_pattern_104 : pattern_104_stmt := by
  intro target h
  cases h with
  | goal_196 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_3
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

