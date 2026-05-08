/- Auto-generated segment pattern proof file.
   Segment pattern: 8
   Goals per instance: 3
   Instances: 12
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_8_instance_1_goalIds : List Nat := [342, 343, 344]
def segment_pattern_8_instance_1_stmt : Prop :=
  goal_342_stmt ∧ (goal_343_stmt ∧ (goal_344_stmt))

def segment_pattern_8_instance_2_goalIds : List Nat := [377, 378, 379]
def segment_pattern_8_instance_2_stmt : Prop :=
  goal_377_stmt ∧ (goal_378_stmt ∧ (goal_379_stmt))

def segment_pattern_8_instance_3_goalIds : List Nat := [412, 413, 414]
def segment_pattern_8_instance_3_stmt : Prop :=
  goal_412_stmt ∧ (goal_413_stmt ∧ (goal_414_stmt))

def segment_pattern_8_instance_4_goalIds : List Nat := [447, 448, 449]
def segment_pattern_8_instance_4_stmt : Prop :=
  goal_447_stmt ∧ (goal_448_stmt ∧ (goal_449_stmt))

def segment_pattern_8_instance_5_goalIds : List Nat := [482, 483, 484]
def segment_pattern_8_instance_5_stmt : Prop :=
  goal_482_stmt ∧ (goal_483_stmt ∧ (goal_484_stmt))

def segment_pattern_8_instance_6_goalIds : List Nat := [517, 518, 519]
def segment_pattern_8_instance_6_stmt : Prop :=
  goal_517_stmt ∧ (goal_518_stmt ∧ (goal_519_stmt))

def segment_pattern_8_instance_7_goalIds : List Nat := [552, 553, 554]
def segment_pattern_8_instance_7_stmt : Prop :=
  goal_552_stmt ∧ (goal_553_stmt ∧ (goal_554_stmt))

def segment_pattern_8_instance_8_goalIds : List Nat := [587, 588, 589]
def segment_pattern_8_instance_8_stmt : Prop :=
  goal_587_stmt ∧ (goal_588_stmt ∧ (goal_589_stmt))

def segment_pattern_8_instance_9_goalIds : List Nat := [622, 623, 624]
def segment_pattern_8_instance_9_stmt : Prop :=
  goal_622_stmt ∧ (goal_623_stmt ∧ (goal_624_stmt))

def segment_pattern_8_instance_10_goalIds : List Nat := [657, 658, 659]
def segment_pattern_8_instance_10_stmt : Prop :=
  goal_657_stmt ∧ (goal_658_stmt ∧ (goal_659_stmt))

def segment_pattern_8_instance_11_goalIds : List Nat := [692, 693, 694]
def segment_pattern_8_instance_11_stmt : Prop :=
  goal_692_stmt ∧ (goal_693_stmt ∧ (goal_694_stmt))

def segment_pattern_8_instance_12_goalIds : List Nat := [727, 728, 729]
def segment_pattern_8_instance_12_stmt : Prop :=
  goal_727_stmt ∧ (goal_728_stmt ∧ (goal_729_stmt))

inductive segment_pattern_8_target : Prop → Prop
  | inst_1 : segment_pattern_8_target segment_pattern_8_instance_1_stmt
  | inst_2 : segment_pattern_8_target segment_pattern_8_instance_2_stmt
  | inst_3 : segment_pattern_8_target segment_pattern_8_instance_3_stmt
  | inst_4 : segment_pattern_8_target segment_pattern_8_instance_4_stmt
  | inst_5 : segment_pattern_8_target segment_pattern_8_instance_5_stmt
  | inst_6 : segment_pattern_8_target segment_pattern_8_instance_6_stmt
  | inst_7 : segment_pattern_8_target segment_pattern_8_instance_7_stmt
  | inst_8 : segment_pattern_8_target segment_pattern_8_instance_8_stmt
  | inst_9 : segment_pattern_8_target segment_pattern_8_instance_9_stmt
  | inst_10 : segment_pattern_8_target segment_pattern_8_instance_10_stmt
  | inst_11 : segment_pattern_8_target segment_pattern_8_instance_11_stmt
  | inst_12 : segment_pattern_8_target segment_pattern_8_instance_12_stmt

def segment_pattern_8_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_8_target target → target
theorem prove_segment_pattern_8 : segment_pattern_8_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

