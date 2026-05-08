/- Auto-generated segment pattern proof file.
   Segment pattern: 3
   Goals per instance: 8
   Instances: 12
   Representative op scale: instances=12, goals/instance=8, ops/instance: SM=8, PM=49, ops=[OpName.FW_transpose, OpName.FW_contiguous, OpName.AllToAllPrim, OpName.AllGatherPrim, OpName.FW_view, OpName.FW_linear, OpName.ChunkPrim, OpName.AllReducePrim, ...]
-/
import denote.gpt2_small_ly12_segments.GeneratedData

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

def segment_pattern_3_instance_5_goalIds : List Nat := [120, 121, 122, 123, 124, 125, 126, 127]
def segment_pattern_3_instance_5_stmt : Prop :=
  goal_120_stmt ∧ (goal_121_stmt ∧ (goal_122_stmt ∧ (goal_123_stmt ∧ (goal_124_stmt ∧ (goal_125_stmt ∧ (goal_126_stmt ∧ (goal_127_stmt)))))))

def segment_pattern_3_instance_6_goalIds : List Nat := [145, 146, 147, 148, 149, 150, 151, 152]
def segment_pattern_3_instance_6_stmt : Prop :=
  goal_145_stmt ∧ (goal_146_stmt ∧ (goal_147_stmt ∧ (goal_148_stmt ∧ (goal_149_stmt ∧ (goal_150_stmt ∧ (goal_151_stmt ∧ (goal_152_stmt)))))))

def segment_pattern_3_instance_7_goalIds : List Nat := [170, 171, 172, 173, 174, 175, 176, 177]
def segment_pattern_3_instance_7_stmt : Prop :=
  goal_170_stmt ∧ (goal_171_stmt ∧ (goal_172_stmt ∧ (goal_173_stmt ∧ (goal_174_stmt ∧ (goal_175_stmt ∧ (goal_176_stmt ∧ (goal_177_stmt)))))))

def segment_pattern_3_instance_8_goalIds : List Nat := [195, 196, 197, 198, 199, 200, 201, 202]
def segment_pattern_3_instance_8_stmt : Prop :=
  goal_195_stmt ∧ (goal_196_stmt ∧ (goal_197_stmt ∧ (goal_198_stmt ∧ (goal_199_stmt ∧ (goal_200_stmt ∧ (goal_201_stmt ∧ (goal_202_stmt)))))))

def segment_pattern_3_instance_9_goalIds : List Nat := [220, 221, 222, 223, 224, 225, 226, 227]
def segment_pattern_3_instance_9_stmt : Prop :=
  goal_220_stmt ∧ (goal_221_stmt ∧ (goal_222_stmt ∧ (goal_223_stmt ∧ (goal_224_stmt ∧ (goal_225_stmt ∧ (goal_226_stmt ∧ (goal_227_stmt)))))))

def segment_pattern_3_instance_10_goalIds : List Nat := [245, 246, 247, 248, 249, 250, 251, 252]
def segment_pattern_3_instance_10_stmt : Prop :=
  goal_245_stmt ∧ (goal_246_stmt ∧ (goal_247_stmt ∧ (goal_248_stmt ∧ (goal_249_stmt ∧ (goal_250_stmt ∧ (goal_251_stmt ∧ (goal_252_stmt)))))))

def segment_pattern_3_instance_11_goalIds : List Nat := [270, 271, 272, 273, 274, 275, 276, 277]
def segment_pattern_3_instance_11_stmt : Prop :=
  goal_270_stmt ∧ (goal_271_stmt ∧ (goal_272_stmt ∧ (goal_273_stmt ∧ (goal_274_stmt ∧ (goal_275_stmt ∧ (goal_276_stmt ∧ (goal_277_stmt)))))))

def segment_pattern_3_instance_12_goalIds : List Nat := [295, 296, 297, 298, 299, 300, 301, 302]
def segment_pattern_3_instance_12_stmt : Prop :=
  goal_295_stmt ∧ (goal_296_stmt ∧ (goal_297_stmt ∧ (goal_298_stmt ∧ (goal_299_stmt ∧ (goal_300_stmt ∧ (goal_301_stmt ∧ (goal_302_stmt)))))))

inductive segment_pattern_3_target : Prop → Prop
  | inst_1 : segment_pattern_3_target segment_pattern_3_instance_1_stmt
  | inst_2 : segment_pattern_3_target segment_pattern_3_instance_2_stmt
  | inst_3 : segment_pattern_3_target segment_pattern_3_instance_3_stmt
  | inst_4 : segment_pattern_3_target segment_pattern_3_instance_4_stmt
  | inst_5 : segment_pattern_3_target segment_pattern_3_instance_5_stmt
  | inst_6 : segment_pattern_3_target segment_pattern_3_instance_6_stmt
  | inst_7 : segment_pattern_3_target segment_pattern_3_instance_7_stmt
  | inst_8 : segment_pattern_3_target segment_pattern_3_instance_8_stmt
  | inst_9 : segment_pattern_3_target segment_pattern_3_instance_9_stmt
  | inst_10 : segment_pattern_3_target segment_pattern_3_instance_10_stmt
  | inst_11 : segment_pattern_3_target segment_pattern_3_instance_11_stmt
  | inst_12 : segment_pattern_3_target segment_pattern_3_instance_12_stmt

def segment_pattern_3_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_3_target target → target
theorem prove_segment_pattern_3 : segment_pattern_3_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

