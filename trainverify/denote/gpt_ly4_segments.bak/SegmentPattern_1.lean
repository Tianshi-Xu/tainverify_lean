/- Auto-generated segment pattern proof file.
   Segment pattern: 1
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=48, ops=[OpName.FW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.FW_layernorm, OpName.FW_linear, OpName.AllGatherPrim, OpName.FW_view, ...]
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Instances

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_1_instance_1_goalIds : List Nat := [4, 5, 6, 7, 8, 9, 10, 11]
def segment_pattern_1_instance_1_stmt : Prop :=
  goal_4_stmt ∧ (goal_5_stmt ∧ (goal_6_stmt ∧ (goal_7_stmt ∧ (goal_8_stmt ∧ (goal_9_stmt ∧ (goal_10_stmt ∧ (goal_11_stmt)))))))

def segment_pattern_1_instance_2_goalIds : List Nat := [29, 30, 31, 32, 33, 34, 35, 36]
def segment_pattern_1_instance_2_stmt : Prop :=
  goal_29_stmt ∧ (goal_30_stmt ∧ (goal_31_stmt ∧ (goal_32_stmt ∧ (goal_33_stmt ∧ (goal_34_stmt ∧ (goal_35_stmt ∧ (goal_36_stmt)))))))

def segment_pattern_1_instance_3_goalIds : List Nat := [54, 55, 56, 57, 58, 59, 60, 61]
def segment_pattern_1_instance_3_stmt : Prop :=
  goal_54_stmt ∧ (goal_55_stmt ∧ (goal_56_stmt ∧ (goal_57_stmt ∧ (goal_58_stmt ∧ (goal_59_stmt ∧ (goal_60_stmt ∧ (goal_61_stmt)))))))

def segment_pattern_1_instance_4_goalIds : List Nat := [79, 80, 81, 82, 83, 84, 85, 86]
def segment_pattern_1_instance_4_stmt : Prop :=
  goal_79_stmt ∧ (goal_80_stmt ∧ (goal_81_stmt ∧ (goal_82_stmt ∧ (goal_83_stmt ∧ (goal_84_stmt ∧ (goal_85_stmt ∧ (goal_86_stmt)))))))

inductive segment_pattern_1_target : Prop → Prop
  | inst_1 : segment_pattern_1_target segment_pattern_1_instance_1_stmt
  | inst_2 : segment_pattern_1_target segment_pattern_1_instance_2_stmt
  | inst_3 : segment_pattern_1_target segment_pattern_1_instance_3_stmt
  | inst_4 : segment_pattern_1_target segment_pattern_1_instance_4_stmt

def segment_pattern_1_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_1_target target → target
theorem prove_segment_pattern_1 : segment_pattern_1_stmt := by
  intro target h
  cases h with
  | inst_1 => exact ⟨prove_goal_4_from_pattern_4, prove_goal_5_from_pattern_5, prove_goal_6_from_pattern_6, prove_goal_7_from_pattern_6, prove_goal_8_from_pattern_7, prove_goal_9_from_pattern_8, prove_goal_10_from_pattern_9, prove_goal_11_from_pattern_8⟩
  | inst_2 => exact ⟨prove_goal_29_from_pattern_24, prove_goal_30_from_pattern_5, prove_goal_31_from_pattern_25, prove_goal_32_from_pattern_6, prove_goal_33_from_pattern_25, prove_goal_34_from_pattern_8, prove_goal_35_from_pattern_26, prove_goal_36_from_pattern_8⟩
  | inst_3 => exact ⟨prove_goal_54_from_pattern_36, prove_goal_55_from_pattern_5, prove_goal_56_from_pattern_7, prove_goal_57_from_pattern_7, prove_goal_58_from_pattern_6, prove_goal_59_from_pattern_8, prove_goal_60_from_pattern_10, prove_goal_61_from_pattern_8⟩
  | inst_4 => exact ⟨prove_goal_79_from_pattern_44, prove_goal_80_from_pattern_5, prove_goal_81_from_pattern_25, prove_goal_82_from_pattern_25, prove_goal_83_from_pattern_6, prove_goal_84_from_pattern_8, prove_goal_85_from_pattern_10, prove_goal_86_from_pattern_8⟩

end TrainVerify.Denote.GeneratedSegmentPatterns

