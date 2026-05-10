/- Auto-generated segment pattern proof file.
   Segment pattern: 8
   Goals per instance: 3
   Instances: 4
   Representative op scale: instances=4, goals/instance=3, ops/instance: SM=3, PM=25, ops=[OpName.BW_gelu, OpName.BW_linear, OpName.AllToAllPrim, OpName.CROSS_DP_WRED]
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Instances

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_8_instance_1_goalIds : List Nat := [142, 143, 144]
def segment_pattern_8_instance_1_stmt : Prop :=
  goal_142_stmt ∧ (goal_143_stmt ∧ (goal_144_stmt))

def segment_pattern_8_instance_2_goalIds : List Nat := [177, 178, 179]
def segment_pattern_8_instance_2_stmt : Prop :=
  goal_177_stmt ∧ (goal_178_stmt ∧ (goal_179_stmt))

def segment_pattern_8_instance_3_goalIds : List Nat := [212, 213, 214]
def segment_pattern_8_instance_3_stmt : Prop :=
  goal_212_stmt ∧ (goal_213_stmt ∧ (goal_214_stmt))

def segment_pattern_8_instance_4_goalIds : List Nat := [247, 248, 249]
def segment_pattern_8_instance_4_stmt : Prop :=
  goal_247_stmt ∧ (goal_248_stmt ∧ (goal_249_stmt))

inductive segment_pattern_8_target : Prop → Prop
  | inst_1 : segment_pattern_8_target segment_pattern_8_instance_1_stmt
  | inst_2 : segment_pattern_8_target segment_pattern_8_instance_2_stmt
  | inst_3 : segment_pattern_8_target segment_pattern_8_instance_3_stmt
  | inst_4 : segment_pattern_8_target segment_pattern_8_instance_4_stmt

def segment_pattern_8_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_8_target target → target
theorem prove_segment_pattern_8 : segment_pattern_8_stmt := by
  intro target h
  cases h with
  | inst_1 => exact ⟨prove_goal_142_from_pattern_79, prove_goal_143_from_pattern_80, prove_goal_144_from_pattern_81⟩
  | inst_2 => exact ⟨prove_goal_177_from_pattern_98, prove_goal_178_from_pattern_78, prove_goal_179_from_pattern_76⟩
  | inst_3 => exact ⟨prove_goal_212_from_pattern_115, prove_goal_213_from_pattern_113, prove_goal_214_from_pattern_114⟩
  | inst_4 => exact ⟨prove_goal_247_from_pattern_115, prove_goal_248_from_pattern_113, prove_goal_249_from_pattern_114⟩

end TrainVerify.Denote.GeneratedSegmentPatterns

