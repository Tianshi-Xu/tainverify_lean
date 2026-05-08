/- Auto-generated segment pattern proof file.
   Segment pattern: 7
   Goals per instance: 8
   Instances: 4
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_7_instance_1_goalIds : List Nat := [134, 135, 136, 137, 138, 139, 140, 141]
def segment_pattern_7_instance_1_stmt : Prop :=
  goal_134_stmt ∧ (goal_135_stmt ∧ (goal_136_stmt ∧ (goal_137_stmt ∧ (goal_138_stmt ∧ (goal_139_stmt ∧ (goal_140_stmt ∧ (goal_141_stmt)))))))

def segment_pattern_7_instance_2_goalIds : List Nat := [169, 170, 171, 172, 173, 174, 175, 176]
def segment_pattern_7_instance_2_stmt : Prop :=
  goal_169_stmt ∧ (goal_170_stmt ∧ (goal_171_stmt ∧ (goal_172_stmt ∧ (goal_173_stmt ∧ (goal_174_stmt ∧ (goal_175_stmt ∧ (goal_176_stmt)))))))

def segment_pattern_7_instance_3_goalIds : List Nat := [204, 205, 206, 207, 208, 209, 210, 211]
def segment_pattern_7_instance_3_stmt : Prop :=
  goal_204_stmt ∧ (goal_205_stmt ∧ (goal_206_stmt ∧ (goal_207_stmt ∧ (goal_208_stmt ∧ (goal_209_stmt ∧ (goal_210_stmt ∧ (goal_211_stmt)))))))

def segment_pattern_7_instance_4_goalIds : List Nat := [239, 240, 241, 242, 243, 244, 245, 246]
def segment_pattern_7_instance_4_stmt : Prop :=
  goal_239_stmt ∧ (goal_240_stmt ∧ (goal_241_stmt ∧ (goal_242_stmt ∧ (goal_243_stmt ∧ (goal_244_stmt ∧ (goal_245_stmt ∧ (goal_246_stmt)))))))

inductive segment_pattern_7_target : Prop → Prop
  | inst_1 : segment_pattern_7_target segment_pattern_7_instance_1_stmt
  | inst_2 : segment_pattern_7_target segment_pattern_7_instance_2_stmt
  | inst_3 : segment_pattern_7_target segment_pattern_7_instance_3_stmt
  | inst_4 : segment_pattern_7_target segment_pattern_7_instance_4_stmt

def segment_pattern_7_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_7_target target → target
theorem prove_segment_pattern_7 : segment_pattern_7_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

