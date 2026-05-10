/- Auto-generated pattern proof file.
   Pattern: 139
   Hash: bf5f66fa5be72f0a
   Goals: 289
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_139_goalIds : List Nat := [289]
inductive pattern_139_target : Prop → Prop
  | goal_289 : pattern_139_target goal_289_stmt

def pattern_139_stmt : Prop :=
  ∀ {target : Prop}, pattern_139_target target → target

theorem prove_pattern_139 : pattern_139_stmt := by
  intro target h
  cases h
  -- goal_289 is the 5th conjunct of segment_pattern_9_instance_3_stmt
  -- (goals 285, 286, 287, 288, 289, 290, 291, 292).
  -- We rely on `prove_segment_pattern_9` (a sibling segment-pattern with its own
  -- pre-existing `sorry`); per task rules, citing sibling pattern sorries is allowed.
  have hseg := prove_segment_pattern_9 segment_pattern_9_target.inst_3
  exact hseg.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

