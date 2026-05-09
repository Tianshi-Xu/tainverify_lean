/- Auto-generated pattern proof file.
   Pattern: 122
   Hash: 0da2be15a57c889d
   Goals: 235
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_122_goalIds : List Nat := [235]
inductive pattern_122_target : Prop → Prop
  | goal_235 : pattern_122_target goal_235_stmt

def pattern_122_stmt : Prop :=
  ∀ {target : Prop}, pattern_122_target target → target

theorem prove_pattern_122 : pattern_122_stmt := by
  intro target h
  cases h with
  | goal_235 =>
      -- goal_235 is the 5th conjunct of segment_pattern_6_instance_4_stmt
      -- (goals 231, 232, 233, 234, 235, 236, 237, 238).
      have hs := prove_segment_pattern_6 segment_pattern_6_target.inst_4
      exact hs.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

