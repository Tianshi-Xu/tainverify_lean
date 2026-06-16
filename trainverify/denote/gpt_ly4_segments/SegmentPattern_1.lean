/- Auto-generated segment pattern proof file.
   Segment pattern: 1
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=48, ops=[OpName.FW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.FW_layernorm, OpName.FW_linear, OpName.AllGatherPrim, OpName.FW_view, ...]
-/
import denote.gpt_ly4_segments.GeneratedData

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
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

