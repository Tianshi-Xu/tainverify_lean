/- Auto-generated segment pattern proof file.
   Segment pattern: 2
   Goals per instance: 8
   Instances: 4
-/
import denote.gpt_ly4_segments.GeneratedData

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
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

