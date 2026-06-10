/- Auto-generated pattern proof file.
   Pattern: 71
   Hash: 86df561567ca4b6b
   Goals: 130
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.SegmentPattern_6

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedSegmentPatterns

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_71_goalIds : List Nat := [130]
inductive pattern_71_target : Prop → Prop
  | goal_130 : pattern_71_target goal_130_stmt

def pattern_71_stmt : Prop :=
  ∀ {target : Prop}, pattern_71_target target → target

theorem prove_pattern_71 : pattern_71_stmt := by
  intro target h
  cases h
  -- goal_130 is the 5th conjunct of segment_pattern_6_instance_1_stmt
  -- (goals 126, 127, 128, 129, 130, 131, 132, 133).
  have hseg := prove_segment_pattern_6 segment_pattern_6_target.inst_1
  exact hseg.right.right.right.right.left

end TrainVerify.Denote.GeneratedPatterns

