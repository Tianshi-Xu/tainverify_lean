/- Auto-generated segment pattern proof file.
   Segment pattern: 3
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=38, ops=[OpName.FW_transpose, OpName.FW_contiguous, OpName.AllToAllPrim, OpName.AllGatherPrim, OpName.FW_view, OpName.FW_linear, OpName.FW_add, OpName.FW_layernorm, ...]
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Instances

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_3_instance_1_goalIds : List Nat := [20, 21, 22, 23, 24, 25, 26, 27]
def segment_pattern_3_instance_1_stmt : Prop :=
  goal_20_stmt ∧ (goal_21_stmt ∧ (goal_22_stmt ∧ (goal_23_stmt ∧ (goal_24_stmt ∧ (goal_25_stmt ∧ (goal_26_stmt ∧ (goal_27_stmt)))))))

def segment_pattern_3_instance_2_goalIds : List Nat := [45, 46, 47, 48, 49, 50, 51, 52]
def segment_pattern_3_instance_2_stmt : Prop :=
  goal_45_stmt ∧ (goal_46_stmt ∧ (goal_47_stmt ∧ (goal_48_stmt ∧ (goal_49_stmt ∧ (goal_50_stmt ∧ (goal_51_stmt ∧ (goal_52_stmt)))))))

def segment_pattern_3_instance_3_goalIds : List Nat := [70, 71, 72, 73, 74, 75, 76, 77]
def segment_pattern_3_instance_3_stmt : Prop :=
  goal_70_stmt ∧ (goal_71_stmt ∧ (goal_72_stmt ∧ (goal_73_stmt ∧ (goal_74_stmt ∧ (goal_75_stmt ∧ (goal_76_stmt ∧ (goal_77_stmt)))))))

def segment_pattern_3_instance_4_goalIds : List Nat := [95, 96, 97, 98, 99, 100, 101, 102]
def segment_pattern_3_instance_4_stmt : Prop :=
  goal_95_stmt ∧ (goal_96_stmt ∧ (goal_97_stmt ∧ (goal_98_stmt ∧ (goal_99_stmt ∧ (goal_100_stmt ∧ (goal_101_stmt ∧ (goal_102_stmt)))))))

inductive segment_pattern_3_target : Prop → Prop
  | inst_1 : segment_pattern_3_target segment_pattern_3_instance_1_stmt
  | inst_2 : segment_pattern_3_target segment_pattern_3_instance_2_stmt
  | inst_3 : segment_pattern_3_target segment_pattern_3_instance_3_stmt
  | inst_4 : segment_pattern_3_target segment_pattern_3_instance_4_stmt

def segment_pattern_3_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_3_target target → target
theorem prove_segment_pattern_3 : segment_pattern_3_stmt := by
  intro target h
  cases h with
  | inst_1 => exact ⟨prove_goal_20_from_pattern_16, prove_goal_21_from_pattern_17, prove_goal_22_from_pattern_18, prove_goal_23_from_pattern_19, prove_goal_24_from_pattern_20, prove_goal_25_from_pattern_21, prove_goal_26_from_pattern_19, prove_goal_27_from_pattern_22⟩
  | inst_2 => exact ⟨prove_goal_45_from_pattern_32, prove_goal_46_from_pattern_33, prove_goal_47_from_pattern_18, prove_goal_48_from_pattern_34, prove_goal_49_from_pattern_24, prove_goal_50_from_pattern_21, prove_goal_51_from_pattern_19, prove_goal_52_from_pattern_35⟩
  | inst_3 => exact ⟨prove_goal_70_from_pattern_41, prove_goal_71_from_pattern_42, prove_goal_72_from_pattern_18, prove_goal_73_from_pattern_43, prove_goal_74_from_pattern_44, prove_goal_75_from_pattern_5, prove_goal_76_from_pattern_45, prove_goal_77_from_pattern_46⟩
  | inst_4 => exact ⟨prove_goal_95_from_pattern_51, prove_goal_96_from_pattern_52, prove_goal_97_from_pattern_18, prove_goal_98_from_pattern_43, prove_goal_99_from_pattern_44, prove_goal_100_from_pattern_5, prove_goal_101_from_pattern_45, prove_goal_102_from_pattern_46⟩

end TrainVerify.Denote.GeneratedSegmentPatterns

