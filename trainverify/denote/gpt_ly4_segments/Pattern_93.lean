/- Auto-generated pattern proof file.
   Pattern: 93
   Hash: 38db11f8b0e656b3
   Goals: 166
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_93_goalIds : List Nat := [166]
inductive pattern_93_target : Prop → Prop
  | goal_166 : pattern_93_target goal_166_stmt

def pattern_93_stmt : Prop :=
  ∀ {target : Prop}, pattern_93_target target → target

theorem prove_pattern_93 : pattern_93_stmt := by
  intro target h
  cases h
  -- goal_166 is the 6th conjunct of segment_pattern_6_instance_2_stmt
  -- (goals 161, 162, 163, 164, 165, 166, 167, 168).
  -- We rely on `prove_segment_pattern_6` (a sibling segment-pattern with its own
  -- pre-existing `sorry`); per task rules, citing sibling pattern sorries is allowed.
  have hseg := prove_segment_pattern_6 segment_pattern_6_target.inst_2
  exact hseg.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

