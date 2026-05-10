/- Auto-generated segment pattern proof file.
   Segment pattern: 7
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=44, ops=[OpName.BW_linear, OpName.AllReducePrim, OpName.BW_add, OpName.BW_multiref, OpName.AllToAllPrim, OpName.BW_layernorm, OpName.CROSS_DP_WRED, OpName.ChunkPrim]
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Instances

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
  intro target h
  cases h with
  | inst_1 => exact ⟨prove_goal_134_from_pattern_75, prove_goal_135_from_pattern_76, prove_goal_136_from_pattern_77, prove_goal_137_from_pattern_57, prove_goal_138_from_pattern_58, prove_goal_139_from_pattern_59, prove_goal_140_from_pattern_78, prove_goal_141_from_pattern_76⟩
  | inst_2 => exact ⟨prove_goal_169_from_pattern_95, prove_goal_170_from_pattern_96, prove_goal_171_from_pattern_82, prove_goal_172_from_pattern_97, prove_goal_173_from_pattern_58, prove_goal_174_from_pattern_59, prove_goal_175_from_pattern_78, prove_goal_176_from_pattern_76⟩
  | inst_3 => exact ⟨prove_goal_204_from_pattern_110, prove_goal_205_from_pattern_111, prove_goal_206_from_pattern_112, prove_goal_207_from_pattern_100, prove_goal_208_from_pattern_58, prove_goal_209_from_pattern_59, prove_goal_210_from_pattern_113, prove_goal_211_from_pattern_114⟩
  | inst_4 => exact ⟨prove_goal_239_from_pattern_110, prove_goal_240_from_pattern_111, prove_goal_241_from_pattern_112, prove_goal_242_from_pattern_100, prove_goal_243_from_pattern_58, prove_goal_244_from_pattern_59, prove_goal_245_from_pattern_113, prove_goal_246_from_pattern_114⟩

end TrainVerify.Denote.GeneratedSegmentPatterns

