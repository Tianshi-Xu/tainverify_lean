/- Auto-generated segment pattern proof file.
   Segment pattern: 9
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=44, ops=[OpName.FW_multiref, OpName.AllToAllPrim, OpName.BW_layernorm, OpName.BW_add, OpName.BW_linear, OpName.ChunkPrim]
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Instances

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
  intro target h
  cases h with
  | inst_1 => exact ⟨prove_goal_257_from_pattern_127, prove_goal_258_from_pattern_125, prove_goal_259_from_pattern_128, prove_goal_260_from_pattern_77, prove_goal_261_from_pattern_129, prove_goal_262_from_pattern_130, prove_goal_263_from_pattern_129, prove_goal_264_from_pattern_130⟩
  | inst_2 => exact ⟨prove_goal_271_from_pattern_127, prove_goal_272_from_pattern_125, prove_goal_273_from_pattern_128, prove_goal_274_from_pattern_133, prove_goal_275_from_pattern_134, prove_goal_276_from_pattern_84, prove_goal_277_from_pattern_129, prove_goal_278_from_pattern_130⟩
  | inst_3 => exact ⟨prove_goal_285_from_pattern_128, prove_goal_286_from_pattern_125, prove_goal_287_from_pattern_128, prove_goal_288_from_pattern_138, prove_goal_289_from_pattern_139, prove_goal_290_from_pattern_132, prove_goal_291_from_pattern_140, prove_goal_292_from_pattern_132⟩
  | inst_4 => exact ⟨prove_goal_299_from_pattern_128, prove_goal_300_from_pattern_125, prove_goal_301_from_pattern_128, prove_goal_302_from_pattern_138, prove_goal_303_from_pattern_134, prove_goal_304_from_pattern_84, prove_goal_305_from_pattern_141, prove_goal_306_from_pattern_84⟩

end TrainVerify.Denote.GeneratedSegmentPatterns

