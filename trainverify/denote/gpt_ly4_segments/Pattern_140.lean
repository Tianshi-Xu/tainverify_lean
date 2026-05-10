/- Auto-generated pattern proof file.
   Pattern: 140
   Hash: 35b9a84bfd883df5
   Goals: 291
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_9

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_140_goalIds : List Nat := [291]
inductive pattern_140_target : Prop → Prop
  | goal_291 : pattern_140_target goal_291_stmt

def pattern_140_stmt : Prop :=
  ∀ {target : Prop}, pattern_140_target target → target

theorem prove_pattern_140 : pattern_140_stmt := by
  intro target h
  cases h
  -- goal_291 is the 7th conjunct of segment_pattern_9_instance_3_stmt
  -- (goals 285, 286, 287, 288, 289, 290, 291, 292).
  have hseg := prove_segment_pattern_9 segment_pattern_9_target.inst_3
  exact hseg.right.right.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

