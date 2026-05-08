/- Auto-generated segment pattern proof file.
   Segment pattern: 1
   Goals per instance: 8
   Instances: 12
   Representative op scale: instances=12, goals/instance=8, ops/instance: SM=8, PM=49, ops=[OpName.FW_add, OpName.AllToAllPrim, OpName.AllReducePrim, OpName.ChunkPrim, OpName.FW_layernorm, OpName.FW_linear, OpName.AllGatherPrim, OpName.FW_view, ...]
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_1_instance_1_goalIds : List Nat := [4, 5, 6, 7, 8, 9, 10, 11]
def segment_pattern_1_instance_1_stmt : Prop :=
  goal_4_stmt ∧ (goal_5_stmt ∧ (goal_6_stmt ∧ (goal_7_stmt ∧ (goal_8_stmt ∧ (goal_9_stmt ∧ (goal_10_stmt ∧ (goal_11_stmt)))))))

def segment_pattern_1_instance_2_goalIds : List Nat := [29, 30, 31, 32, 33, 34, 35, 36]
def segment_pattern_1_instance_2_stmt : Prop :=
  goal_29_stmt ∧ (goal_30_stmt ∧ (goal_31_stmt ∧ (goal_32_stmt ∧ (goal_33_stmt ∧ (goal_34_stmt ∧ (goal_35_stmt ∧ (goal_36_stmt)))))))

def segment_pattern_1_instance_3_goalIds : List Nat := [54, 55, 56, 57, 58, 59, 60, 61]
def segment_pattern_1_instance_3_stmt : Prop :=
  goal_54_stmt ∧ (goal_55_stmt ∧ (goal_56_stmt ∧ (goal_57_stmt ∧ (goal_58_stmt ∧ (goal_59_stmt ∧ (goal_60_stmt ∧ (goal_61_stmt)))))))

def segment_pattern_1_instance_4_goalIds : List Nat := [79, 80, 81, 82, 83, 84, 85, 86]
def segment_pattern_1_instance_4_stmt : Prop :=
  goal_79_stmt ∧ (goal_80_stmt ∧ (goal_81_stmt ∧ (goal_82_stmt ∧ (goal_83_stmt ∧ (goal_84_stmt ∧ (goal_85_stmt ∧ (goal_86_stmt)))))))

def segment_pattern_1_instance_5_goalIds : List Nat := [104, 105, 106, 107, 108, 109, 110, 111]
def segment_pattern_1_instance_5_stmt : Prop :=
  goal_104_stmt ∧ (goal_105_stmt ∧ (goal_106_stmt ∧ (goal_107_stmt ∧ (goal_108_stmt ∧ (goal_109_stmt ∧ (goal_110_stmt ∧ (goal_111_stmt)))))))

def segment_pattern_1_instance_6_goalIds : List Nat := [129, 130, 131, 132, 133, 134, 135, 136]
def segment_pattern_1_instance_6_stmt : Prop :=
  goal_129_stmt ∧ (goal_130_stmt ∧ (goal_131_stmt ∧ (goal_132_stmt ∧ (goal_133_stmt ∧ (goal_134_stmt ∧ (goal_135_stmt ∧ (goal_136_stmt)))))))

def segment_pattern_1_instance_7_goalIds : List Nat := [154, 155, 156, 157, 158, 159, 160, 161]
def segment_pattern_1_instance_7_stmt : Prop :=
  goal_154_stmt ∧ (goal_155_stmt ∧ (goal_156_stmt ∧ (goal_157_stmt ∧ (goal_158_stmt ∧ (goal_159_stmt ∧ (goal_160_stmt ∧ (goal_161_stmt)))))))

def segment_pattern_1_instance_8_goalIds : List Nat := [179, 180, 181, 182, 183, 184, 185, 186]
def segment_pattern_1_instance_8_stmt : Prop :=
  goal_179_stmt ∧ (goal_180_stmt ∧ (goal_181_stmt ∧ (goal_182_stmt ∧ (goal_183_stmt ∧ (goal_184_stmt ∧ (goal_185_stmt ∧ (goal_186_stmt)))))))

def segment_pattern_1_instance_9_goalIds : List Nat := [204, 205, 206, 207, 208, 209, 210, 211]
def segment_pattern_1_instance_9_stmt : Prop :=
  goal_204_stmt ∧ (goal_205_stmt ∧ (goal_206_stmt ∧ (goal_207_stmt ∧ (goal_208_stmt ∧ (goal_209_stmt ∧ (goal_210_stmt ∧ (goal_211_stmt)))))))

def segment_pattern_1_instance_10_goalIds : List Nat := [229, 230, 231, 232, 233, 234, 235, 236]
def segment_pattern_1_instance_10_stmt : Prop :=
  goal_229_stmt ∧ (goal_230_stmt ∧ (goal_231_stmt ∧ (goal_232_stmt ∧ (goal_233_stmt ∧ (goal_234_stmt ∧ (goal_235_stmt ∧ (goal_236_stmt)))))))

def segment_pattern_1_instance_11_goalIds : List Nat := [254, 255, 256, 257, 258, 259, 260, 261]
def segment_pattern_1_instance_11_stmt : Prop :=
  goal_254_stmt ∧ (goal_255_stmt ∧ (goal_256_stmt ∧ (goal_257_stmt ∧ (goal_258_stmt ∧ (goal_259_stmt ∧ (goal_260_stmt ∧ (goal_261_stmt)))))))

def segment_pattern_1_instance_12_goalIds : List Nat := [279, 280, 281, 282, 283, 284, 285, 286]
def segment_pattern_1_instance_12_stmt : Prop :=
  goal_279_stmt ∧ (goal_280_stmt ∧ (goal_281_stmt ∧ (goal_282_stmt ∧ (goal_283_stmt ∧ (goal_284_stmt ∧ (goal_285_stmt ∧ (goal_286_stmt)))))))

inductive segment_pattern_1_target : Prop → Prop
  | inst_1 : segment_pattern_1_target segment_pattern_1_instance_1_stmt
  | inst_2 : segment_pattern_1_target segment_pattern_1_instance_2_stmt
  | inst_3 : segment_pattern_1_target segment_pattern_1_instance_3_stmt
  | inst_4 : segment_pattern_1_target segment_pattern_1_instance_4_stmt
  | inst_5 : segment_pattern_1_target segment_pattern_1_instance_5_stmt
  | inst_6 : segment_pattern_1_target segment_pattern_1_instance_6_stmt
  | inst_7 : segment_pattern_1_target segment_pattern_1_instance_7_stmt
  | inst_8 : segment_pattern_1_target segment_pattern_1_instance_8_stmt
  | inst_9 : segment_pattern_1_target segment_pattern_1_instance_9_stmt
  | inst_10 : segment_pattern_1_target segment_pattern_1_instance_10_stmt
  | inst_11 : segment_pattern_1_target segment_pattern_1_instance_11_stmt
  | inst_12 : segment_pattern_1_target segment_pattern_1_instance_12_stmt

def segment_pattern_1_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_1_target target → target
theorem prove_segment_pattern_1 : segment_pattern_1_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

