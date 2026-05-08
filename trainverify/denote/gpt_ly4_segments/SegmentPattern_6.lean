/- Auto-generated segment pattern proof file.
   Segment pattern: 6
   Goals per instance: 8
   Instances: 4
-/
import denote.gpt_ly4_segments.GeneratedData

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
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

