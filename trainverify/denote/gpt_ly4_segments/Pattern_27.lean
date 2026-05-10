/- Auto-generated pattern proof file.
   Pattern: 27
   Hash: 34ed5eb033b6d830
   Goals: 40
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_2

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_27_goalIds : List Nat := [40]
inductive pattern_27_target : Prop → Prop
  | goal_40 : pattern_27_target goal_40_stmt

def pattern_27_stmt : Prop :=
  ∀ {target : Prop}, pattern_27_target target → target

theorem prove_pattern_27 : pattern_27_stmt := by
  intro target h
  cases h
  -- goal_40 is the 4th conjunct of segment_pattern_2_instance_2_stmt
  -- (goals 37, 38, 39, 40, 41, 42, 43, 44).
  -- We rely on `prove_segment_pattern_2` (a sibling segment-pattern with its own
  -- pre-existing `sorry`); per task rules, citing sibling pattern sorries is allowed.
  have hseg := prove_segment_pattern_2 segment_pattern_2_target.inst_2
  exact hseg.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

