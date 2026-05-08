/- Auto-generated segment pattern proof file.
   Segment pattern: 2
   Goals per instance: 8
   Instances: 12
-/
import denote.gpt2_small_ly12_segments.GeneratedData

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

def segment_pattern_2_instance_5_goalIds : List Nat := [112, 113, 114, 115, 116, 117, 118, 119]
def segment_pattern_2_instance_5_stmt : Prop :=
  goal_112_stmt ∧ (goal_113_stmt ∧ (goal_114_stmt ∧ (goal_115_stmt ∧ (goal_116_stmt ∧ (goal_117_stmt ∧ (goal_118_stmt ∧ (goal_119_stmt)))))))

def segment_pattern_2_instance_6_goalIds : List Nat := [137, 138, 139, 140, 141, 142, 143, 144]
def segment_pattern_2_instance_6_stmt : Prop :=
  goal_137_stmt ∧ (goal_138_stmt ∧ (goal_139_stmt ∧ (goal_140_stmt ∧ (goal_141_stmt ∧ (goal_142_stmt ∧ (goal_143_stmt ∧ (goal_144_stmt)))))))

def segment_pattern_2_instance_7_goalIds : List Nat := [162, 163, 164, 165, 166, 167, 168, 169]
def segment_pattern_2_instance_7_stmt : Prop :=
  goal_162_stmt ∧ (goal_163_stmt ∧ (goal_164_stmt ∧ (goal_165_stmt ∧ (goal_166_stmt ∧ (goal_167_stmt ∧ (goal_168_stmt ∧ (goal_169_stmt)))))))

def segment_pattern_2_instance_8_goalIds : List Nat := [187, 188, 189, 190, 191, 192, 193, 194]
def segment_pattern_2_instance_8_stmt : Prop :=
  goal_187_stmt ∧ (goal_188_stmt ∧ (goal_189_stmt ∧ (goal_190_stmt ∧ (goal_191_stmt ∧ (goal_192_stmt ∧ (goal_193_stmt ∧ (goal_194_stmt)))))))

def segment_pattern_2_instance_9_goalIds : List Nat := [212, 213, 214, 215, 216, 217, 218, 219]
def segment_pattern_2_instance_9_stmt : Prop :=
  goal_212_stmt ∧ (goal_213_stmt ∧ (goal_214_stmt ∧ (goal_215_stmt ∧ (goal_216_stmt ∧ (goal_217_stmt ∧ (goal_218_stmt ∧ (goal_219_stmt)))))))

def segment_pattern_2_instance_10_goalIds : List Nat := [237, 238, 239, 240, 241, 242, 243, 244]
def segment_pattern_2_instance_10_stmt : Prop :=
  goal_237_stmt ∧ (goal_238_stmt ∧ (goal_239_stmt ∧ (goal_240_stmt ∧ (goal_241_stmt ∧ (goal_242_stmt ∧ (goal_243_stmt ∧ (goal_244_stmt)))))))

def segment_pattern_2_instance_11_goalIds : List Nat := [262, 263, 264, 265, 266, 267, 268, 269]
def segment_pattern_2_instance_11_stmt : Prop :=
  goal_262_stmt ∧ (goal_263_stmt ∧ (goal_264_stmt ∧ (goal_265_stmt ∧ (goal_266_stmt ∧ (goal_267_stmt ∧ (goal_268_stmt ∧ (goal_269_stmt)))))))

def segment_pattern_2_instance_12_goalIds : List Nat := [287, 288, 289, 290, 291, 292, 293, 294]
def segment_pattern_2_instance_12_stmt : Prop :=
  goal_287_stmt ∧ (goal_288_stmt ∧ (goal_289_stmt ∧ (goal_290_stmt ∧ (goal_291_stmt ∧ (goal_292_stmt ∧ (goal_293_stmt ∧ (goal_294_stmt)))))))

inductive segment_pattern_2_target : Prop → Prop
  | inst_1 : segment_pattern_2_target segment_pattern_2_instance_1_stmt
  | inst_2 : segment_pattern_2_target segment_pattern_2_instance_2_stmt
  | inst_3 : segment_pattern_2_target segment_pattern_2_instance_3_stmt
  | inst_4 : segment_pattern_2_target segment_pattern_2_instance_4_stmt
  | inst_5 : segment_pattern_2_target segment_pattern_2_instance_5_stmt
  | inst_6 : segment_pattern_2_target segment_pattern_2_instance_6_stmt
  | inst_7 : segment_pattern_2_target segment_pattern_2_instance_7_stmt
  | inst_8 : segment_pattern_2_target segment_pattern_2_instance_8_stmt
  | inst_9 : segment_pattern_2_target segment_pattern_2_instance_9_stmt
  | inst_10 : segment_pattern_2_target segment_pattern_2_instance_10_stmt
  | inst_11 : segment_pattern_2_target segment_pattern_2_instance_11_stmt
  | inst_12 : segment_pattern_2_target segment_pattern_2_instance_12_stmt

def segment_pattern_2_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_2_target target → target
theorem prove_segment_pattern_2 : segment_pattern_2_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

