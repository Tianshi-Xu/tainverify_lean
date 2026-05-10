/- Auto-generated segment pattern proof file.
   Segment pattern: 4
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=66, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.BW_multiref, OpName.BW_layernorm, OpName.CROSS_DP_WRED, OpName.BW_linear, ...]
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Instances

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_4_instance_1_goalIds : List Nat := [110, 111, 112, 113, 114, 115, 116, 117]
def segment_pattern_4_instance_1_stmt : Prop :=
  goal_110_stmt ∧ (goal_111_stmt ∧ (goal_112_stmt ∧ (goal_113_stmt ∧ (goal_114_stmt ∧ (goal_115_stmt ∧ (goal_116_stmt ∧ (goal_117_stmt)))))))

def segment_pattern_4_instance_2_goalIds : List Nat := [145, 146, 147, 148, 149, 150, 151, 152]
def segment_pattern_4_instance_2_stmt : Prop :=
  goal_145_stmt ∧ (goal_146_stmt ∧ (goal_147_stmt ∧ (goal_148_stmt ∧ (goal_149_stmt ∧ (goal_150_stmt ∧ (goal_151_stmt ∧ (goal_152_stmt)))))))

def segment_pattern_4_instance_3_goalIds : List Nat := [180, 181, 182, 183, 184, 185, 186, 187]
def segment_pattern_4_instance_3_stmt : Prop :=
  goal_180_stmt ∧ (goal_181_stmt ∧ (goal_182_stmt ∧ (goal_183_stmt ∧ (goal_184_stmt ∧ (goal_185_stmt ∧ (goal_186_stmt ∧ (goal_187_stmt)))))))

def segment_pattern_4_instance_4_goalIds : List Nat := [215, 216, 217, 218, 219, 220, 221, 222]
def segment_pattern_4_instance_4_stmt : Prop :=
  goal_215_stmt ∧ (goal_216_stmt ∧ (goal_217_stmt ∧ (goal_218_stmt ∧ (goal_219_stmt ∧ (goal_220_stmt ∧ (goal_221_stmt ∧ (goal_222_stmt)))))))

inductive segment_pattern_4_target : Prop → Prop
  | inst_1 : segment_pattern_4_target segment_pattern_4_instance_1_stmt
  | inst_2 : segment_pattern_4_target segment_pattern_4_instance_2_stmt
  | inst_3 : segment_pattern_4_target segment_pattern_4_instance_3_stmt
  | inst_4 : segment_pattern_4_target segment_pattern_4_instance_4_stmt

def segment_pattern_4_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_4_target target → target
theorem prove_segment_pattern_4 : segment_pattern_4_stmt := by
  intro target h
  cases h with
  | inst_1 => exact ⟨prove_goal_110_from_pattern_56, prove_goal_111_from_pattern_57, prove_goal_112_from_pattern_58, prove_goal_113_from_pattern_59, prove_goal_114_from_pattern_60, prove_goal_115_from_pattern_61, prove_goal_116_from_pattern_62, prove_goal_117_from_pattern_61⟩
  | inst_2 => exact ⟨prove_goal_145_from_pattern_82, prove_goal_146_from_pattern_57, prove_goal_147_from_pattern_58, prove_goal_148_from_pattern_59, prove_goal_149_from_pattern_83, prove_goal_150_from_pattern_84, prove_goal_151_from_pattern_62, prove_goal_152_from_pattern_61⟩
  | inst_3 => exact ⟨prove_goal_180_from_pattern_99, prove_goal_181_from_pattern_100, prove_goal_182_from_pattern_58, prove_goal_183_from_pattern_59, prove_goal_184_from_pattern_101, prove_goal_185_from_pattern_63, prove_goal_186_from_pattern_62, prove_goal_187_from_pattern_63⟩
  | inst_4 => exact ⟨prove_goal_215_from_pattern_112, prove_goal_216_from_pattern_100, prove_goal_217_from_pattern_58, prove_goal_218_from_pattern_59, prove_goal_219_from_pattern_116, prove_goal_220_from_pattern_84, prove_goal_221_from_pattern_62, prove_goal_222_from_pattern_84⟩

end TrainVerify.Denote.GeneratedSegmentPatterns

