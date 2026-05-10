/- Auto-generated segment pattern proof file.
   Segment pattern: 6
   Goals per instance: 8
   Instances: 4
   Representative op scale: instances=4, goals/instance=8, ops/instance: SM=8, PM=63, ops=[OpName.BW_matmul, OpName.BW_div, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim, OpName.BW_softmax, OpName.AllToAllPrim, OpName.BW_transpose, ...]
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Instances

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_6_instance_1_goalIds : List Nat := [126, 127, 128, 129, 130, 131, 132, 133]
def segment_pattern_6_instance_1_stmt : Prop :=
  goal_126_stmt ∧ (goal_127_stmt ∧ (goal_128_stmt ∧ (goal_129_stmt ∧ (goal_130_stmt ∧ (goal_131_stmt ∧ (goal_132_stmt ∧ (goal_133_stmt)))))))

def segment_pattern_6_instance_2_goalIds : List Nat := [161, 162, 163, 164, 165, 166, 167, 168]
def segment_pattern_6_instance_2_stmt : Prop :=
  goal_161_stmt ∧ (goal_162_stmt ∧ (goal_163_stmt ∧ (goal_164_stmt ∧ (goal_165_stmt ∧ (goal_166_stmt ∧ (goal_167_stmt ∧ (goal_168_stmt)))))))

def segment_pattern_6_instance_3_goalIds : List Nat := [196, 197, 198, 199, 200, 201, 202, 203]
def segment_pattern_6_instance_3_stmt : Prop :=
  goal_196_stmt ∧ (goal_197_stmt ∧ (goal_198_stmt ∧ (goal_199_stmt ∧ (goal_200_stmt ∧ (goal_201_stmt ∧ (goal_202_stmt ∧ (goal_203_stmt)))))))

def segment_pattern_6_instance_4_goalIds : List Nat := [231, 232, 233, 234, 235, 236, 237, 238]
def segment_pattern_6_instance_4_stmt : Prop :=
  goal_231_stmt ∧ (goal_232_stmt ∧ (goal_233_stmt ∧ (goal_234_stmt ∧ (goal_235_stmt ∧ (goal_236_stmt ∧ (goal_237_stmt ∧ (goal_238_stmt)))))))

inductive segment_pattern_6_target : Prop → Prop
  | inst_1 : segment_pattern_6_target segment_pattern_6_instance_1_stmt
  | inst_2 : segment_pattern_6_target segment_pattern_6_instance_2_stmt
  | inst_3 : segment_pattern_6_target segment_pattern_6_instance_3_stmt
  | inst_4 : segment_pattern_6_target segment_pattern_6_instance_4_stmt

def segment_pattern_6_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_6_target target → target
theorem prove_segment_pattern_6 : segment_pattern_6_stmt := by
  intro target h
  cases h with
  | inst_1 => exact ⟨prove_goal_126_from_pattern_68, prove_goal_127_from_pattern_65, prove_goal_128_from_pattern_69, prove_goal_129_from_pattern_70, prove_goal_130_from_pattern_71, prove_goal_131_from_pattern_72, prove_goal_132_from_pattern_73, prove_goal_133_from_pattern_74⟩
  | inst_2 => exact ⟨prove_goal_161_from_pattern_88, prove_goal_162_from_pattern_89, prove_goal_163_from_pattern_90, prove_goal_164_from_pattern_91, prove_goal_165_from_pattern_92, prove_goal_166_from_pattern_93, prove_goal_167_from_pattern_94, prove_goal_168_from_pattern_74⟩
  | inst_3 => exact ⟨prove_goal_196_from_pattern_104, prove_goal_197_from_pattern_105, prove_goal_198_from_pattern_106, prove_goal_199_from_pattern_91, prove_goal_200_from_pattern_107, prove_goal_201_from_pattern_108, prove_goal_202_from_pattern_109, prove_goal_203_from_pattern_74⟩
  | inst_4 => exact ⟨prove_goal_231_from_pattern_119, prove_goal_232_from_pattern_120, prove_goal_233_from_pattern_90, prove_goal_234_from_pattern_121, prove_goal_235_from_pattern_122, prove_goal_236_from_pattern_123, prove_goal_237_from_pattern_124, prove_goal_238_from_pattern_74⟩

end TrainVerify.Denote.GeneratedSegmentPatterns

