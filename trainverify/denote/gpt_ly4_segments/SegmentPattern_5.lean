/- Auto-generated segment pattern proof file.
   Segment pattern: 5
   Goals per instance: 8
   Instances: 4
-/
import denote.gpt_ly4_segments.GeneratedData

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
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

