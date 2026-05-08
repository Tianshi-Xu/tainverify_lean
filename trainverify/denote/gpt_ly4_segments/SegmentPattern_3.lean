/- Auto-generated segment pattern proof file.
   Segment pattern: 3
   Goals per instance: 8
   Instances: 4
-/
import denote.gpt_ly4_segments.GeneratedData

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
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

