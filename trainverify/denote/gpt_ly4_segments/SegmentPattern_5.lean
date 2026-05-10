/- Auto-generated segment pattern proof file.
   Segment pattern: 5
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=59, ops=[OpName.BW_view, OpName.BW_linear, OpName.ChunkPrim, OpName.BW_transpose, OpName.AllGatherPrim, OpName.BW_matmul, OpName.AllToAllPrim]
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Instances

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_5_instance_1_goalIds : List Nat := [118, 119, 120, 121, 122, 123, 124, 125]
def segment_pattern_5_instance_1_stmt : Prop :=
  goal_118_stmt ∧ (goal_119_stmt ∧ (goal_120_stmt ∧ (goal_121_stmt ∧ (goal_122_stmt ∧ (goal_123_stmt ∧ (goal_124_stmt ∧ (goal_125_stmt)))))))

def segment_pattern_5_instance_2_goalIds : List Nat := [153, 154, 155, 156, 157, 158, 159, 160]
def segment_pattern_5_instance_2_stmt : Prop :=
  goal_153_stmt ∧ (goal_154_stmt ∧ (goal_155_stmt ∧ (goal_156_stmt ∧ (goal_157_stmt ∧ (goal_158_stmt ∧ (goal_159_stmt ∧ (goal_160_stmt)))))))

def segment_pattern_5_instance_3_goalIds : List Nat := [188, 189, 190, 191, 192, 193, 194, 195]
def segment_pattern_5_instance_3_stmt : Prop :=
  goal_188_stmt ∧ (goal_189_stmt ∧ (goal_190_stmt ∧ (goal_191_stmt ∧ (goal_192_stmt ∧ (goal_193_stmt ∧ (goal_194_stmt ∧ (goal_195_stmt)))))))

def segment_pattern_5_instance_4_goalIds : List Nat := [223, 224, 225, 226, 227, 228, 229, 230]
def segment_pattern_5_instance_4_stmt : Prop :=
  goal_223_stmt ∧ (goal_224_stmt ∧ (goal_225_stmt ∧ (goal_226_stmt ∧ (goal_227_stmt ∧ (goal_228_stmt ∧ (goal_229_stmt ∧ (goal_230_stmt)))))))

inductive segment_pattern_5_target : Prop → Prop
  | inst_1 : segment_pattern_5_target segment_pattern_5_instance_1_stmt
  | inst_2 : segment_pattern_5_target segment_pattern_5_instance_2_stmt
  | inst_3 : segment_pattern_5_target segment_pattern_5_instance_3_stmt
  | inst_4 : segment_pattern_5_target segment_pattern_5_instance_4_stmt

def segment_pattern_5_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_5_target target → target
theorem prove_segment_pattern_5 : segment_pattern_5_stmt := by
  intro target h
  cases h with
  | inst_1 => exact ⟨prove_goal_118_from_pattern_62, prove_goal_119_from_pattern_63, prove_goal_120_from_pattern_62, prove_goal_121_from_pattern_64, prove_goal_122_from_pattern_65, prove_goal_123_from_pattern_66, prove_goal_124_from_pattern_67, prove_goal_125_from_pattern_64⟩
  | inst_2 => exact ⟨prove_goal_153_from_pattern_62, prove_goal_154_from_pattern_84, prove_goal_155_from_pattern_62, prove_goal_156_from_pattern_85, prove_goal_157_from_pattern_86, prove_goal_158_from_pattern_66, prove_goal_159_from_pattern_87, prove_goal_160_from_pattern_64⟩
  | inst_3 => exact ⟨prove_goal_188_from_pattern_62, prove_goal_189_from_pattern_61, prove_goal_190_from_pattern_62, prove_goal_191_from_pattern_66, prove_goal_192_from_pattern_102, prove_goal_193_from_pattern_64, prove_goal_194_from_pattern_103, prove_goal_195_from_pattern_85⟩
  | inst_4 => exact ⟨prove_goal_223_from_pattern_62, prove_goal_224_from_pattern_61, prove_goal_225_from_pattern_62, prove_goal_226_from_pattern_66, prove_goal_227_from_pattern_117, prove_goal_228_from_pattern_64, prove_goal_229_from_pattern_118, prove_goal_230_from_pattern_85⟩

end TrainVerify.Denote.GeneratedSegmentPatterns

