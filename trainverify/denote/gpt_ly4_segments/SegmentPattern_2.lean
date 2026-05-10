/- Auto-generated segment pattern proof file.
   Segment pattern: 2
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=55, ops=[OpName.FW_transpose, OpName.ChunkPrim, OpName.FW_view, OpName.AllToAllPrim, OpName.FW_matmul, OpName.AllReducePrim, OpName.FW_div, OpName.FW_softmax, ...]
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Instances

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_2_instance_1_goalIds : List Nat := [12, 13, 14, 15, 16, 17, 18, 19]
def segment_pattern_2_instance_1_stmt : Prop :=
  goal_12_stmt ∧ (goal_13_stmt ∧ (goal_14_stmt ∧ (goal_15_stmt ∧ (goal_16_stmt ∧ (goal_17_stmt ∧ (goal_18_stmt ∧ (goal_19_stmt)))))))

def segment_pattern_2_instance_2_goalIds : List Nat := [37, 38, 39, 40, 41, 42, 43, 44]
def segment_pattern_2_instance_2_stmt : Prop :=
  goal_37_stmt ∧ (goal_38_stmt ∧ (goal_39_stmt ∧ (goal_40_stmt ∧ (goal_41_stmt ∧ (goal_42_stmt ∧ (goal_43_stmt ∧ (goal_44_stmt)))))))

def segment_pattern_2_instance_3_goalIds : List Nat := [62, 63, 64, 65, 66, 67, 68, 69]
def segment_pattern_2_instance_3_stmt : Prop :=
  goal_62_stmt ∧ (goal_63_stmt ∧ (goal_64_stmt ∧ (goal_65_stmt ∧ (goal_66_stmt ∧ (goal_67_stmt ∧ (goal_68_stmt ∧ (goal_69_stmt)))))))

def segment_pattern_2_instance_4_goalIds : List Nat := [87, 88, 89, 90, 91, 92, 93, 94]
def segment_pattern_2_instance_4_stmt : Prop :=
  goal_87_stmt ∧ (goal_88_stmt ∧ (goal_89_stmt ∧ (goal_90_stmt ∧ (goal_91_stmt ∧ (goal_92_stmt ∧ (goal_93_stmt ∧ (goal_94_stmt)))))))

inductive segment_pattern_2_target : Prop → Prop
  | inst_1 : segment_pattern_2_target segment_pattern_2_instance_1_stmt
  | inst_2 : segment_pattern_2_target segment_pattern_2_instance_2_stmt
  | inst_3 : segment_pattern_2_target segment_pattern_2_instance_3_stmt
  | inst_4 : segment_pattern_2_target segment_pattern_2_instance_4_stmt

def segment_pattern_2_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_2_target target → target
theorem prove_segment_pattern_2 : segment_pattern_2_stmt := by
  intro target h
  cases h with
  | inst_1 => exact ⟨prove_goal_12_from_pattern_10, prove_goal_13_from_pattern_8, prove_goal_14_from_pattern_9, prove_goal_15_from_pattern_11, prove_goal_16_from_pattern_12, prove_goal_17_from_pattern_13, prove_goal_18_from_pattern_14, prove_goal_19_from_pattern_15⟩
  | inst_2 => exact ⟨prove_goal_37_from_pattern_10, prove_goal_38_from_pattern_8, prove_goal_39_from_pattern_9, prove_goal_40_from_pattern_27, prove_goal_41_from_pattern_28, prove_goal_42_from_pattern_29, prove_goal_43_from_pattern_30, prove_goal_44_from_pattern_31⟩
  | inst_3 => exact ⟨prove_goal_62_from_pattern_9, prove_goal_63_from_pattern_8, prove_goal_64_from_pattern_26, prove_goal_65_from_pattern_37, prove_goal_66_from_pattern_38, prove_goal_67_from_pattern_39, prove_goal_68_from_pattern_30, prove_goal_69_from_pattern_40⟩
  | inst_4 => exact ⟨prove_goal_87_from_pattern_9, prove_goal_88_from_pattern_8, prove_goal_89_from_pattern_26, prove_goal_90_from_pattern_47, prove_goal_91_from_pattern_48, prove_goal_92_from_pattern_29, prove_goal_93_from_pattern_49, prove_goal_94_from_pattern_50⟩

end TrainVerify.Denote.GeneratedSegmentPatterns

