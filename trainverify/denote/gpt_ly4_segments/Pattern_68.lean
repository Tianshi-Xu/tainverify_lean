/- Auto-generated pattern proof file.
   Pattern: 68
   Hash: b85d28f2a7d35175
   Goals: 126
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote.GeneratedPatterns

def pattern_68_goalIds : List Nat := [126]
inductive pattern_68_target : Prop → Prop
  | goal_126 : pattern_68_target goal_126_stmt

def pattern_68_stmt : Prop :=
  ∀ {target : Prop}, pattern_68_target target → target
theorem prove_pattern_68 : pattern_68_stmt := by
  intro target h
  cases h with
  | goal_126 =>
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_1
      exact hs.left

end TrainVerify.Denote.GeneratedPatterns

