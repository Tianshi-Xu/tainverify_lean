/- Auto-generated segment pattern proof file.
   Segment pattern: 4
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=66, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.BW_multiref, OpName.BW_layernorm, OpName.CROSS_DP_WRED, OpName.BW_linear, ...]
-/
import denote.gpt_ly4_segments.GeneratedData

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
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

