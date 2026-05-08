/- Auto-generated segment pattern proof file.
   Segment pattern: 9
   Goals per instance: 8
   Instances: 4
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_9_instance_1_goalIds : List Nat := [257, 258, 259, 260, 261, 262, 263, 264]
def segment_pattern_9_instance_1_stmt : Prop :=
  goal_257_stmt ∧ (goal_258_stmt ∧ (goal_259_stmt ∧ (goal_260_stmt ∧ (goal_261_stmt ∧ (goal_262_stmt ∧ (goal_263_stmt ∧ (goal_264_stmt)))))))

def segment_pattern_9_instance_2_goalIds : List Nat := [271, 272, 273, 274, 275, 276, 277, 278]
def segment_pattern_9_instance_2_stmt : Prop :=
  goal_271_stmt ∧ (goal_272_stmt ∧ (goal_273_stmt ∧ (goal_274_stmt ∧ (goal_275_stmt ∧ (goal_276_stmt ∧ (goal_277_stmt ∧ (goal_278_stmt)))))))

def segment_pattern_9_instance_3_goalIds : List Nat := [285, 286, 287, 288, 289, 290, 291, 292]
def segment_pattern_9_instance_3_stmt : Prop :=
  goal_285_stmt ∧ (goal_286_stmt ∧ (goal_287_stmt ∧ (goal_288_stmt ∧ (goal_289_stmt ∧ (goal_290_stmt ∧ (goal_291_stmt ∧ (goal_292_stmt)))))))

def segment_pattern_9_instance_4_goalIds : List Nat := [299, 300, 301, 302, 303, 304, 305, 306]
def segment_pattern_9_instance_4_stmt : Prop :=
  goal_299_stmt ∧ (goal_300_stmt ∧ (goal_301_stmt ∧ (goal_302_stmt ∧ (goal_303_stmt ∧ (goal_304_stmt ∧ (goal_305_stmt ∧ (goal_306_stmt)))))))

inductive segment_pattern_9_target : Prop → Prop
  | inst_1 : segment_pattern_9_target segment_pattern_9_instance_1_stmt
  | inst_2 : segment_pattern_9_target segment_pattern_9_instance_2_stmt
  | inst_3 : segment_pattern_9_target segment_pattern_9_instance_3_stmt
  | inst_4 : segment_pattern_9_target segment_pattern_9_instance_4_stmt

def segment_pattern_9_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_9_target target → target
theorem prove_segment_pattern_9 : segment_pattern_9_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

