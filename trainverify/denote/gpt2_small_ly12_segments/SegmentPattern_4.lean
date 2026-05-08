/- Auto-generated segment pattern proof file.
   Segment pattern: 4
   Goals per instance: 8
   Instances: 12
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_4_instance_1_goalIds : List Nat := [310, 311, 312, 313, 314, 315, 316, 317]
def segment_pattern_4_instance_1_stmt : Prop :=
  goal_310_stmt ∧ (goal_311_stmt ∧ (goal_312_stmt ∧ (goal_313_stmt ∧ (goal_314_stmt ∧ (goal_315_stmt ∧ (goal_316_stmt ∧ (goal_317_stmt)))))))

def segment_pattern_4_instance_2_goalIds : List Nat := [345, 346, 347, 348, 349, 350, 351, 352]
def segment_pattern_4_instance_2_stmt : Prop :=
  goal_345_stmt ∧ (goal_346_stmt ∧ (goal_347_stmt ∧ (goal_348_stmt ∧ (goal_349_stmt ∧ (goal_350_stmt ∧ (goal_351_stmt ∧ (goal_352_stmt)))))))

def segment_pattern_4_instance_3_goalIds : List Nat := [380, 381, 382, 383, 384, 385, 386, 387]
def segment_pattern_4_instance_3_stmt : Prop :=
  goal_380_stmt ∧ (goal_381_stmt ∧ (goal_382_stmt ∧ (goal_383_stmt ∧ (goal_384_stmt ∧ (goal_385_stmt ∧ (goal_386_stmt ∧ (goal_387_stmt)))))))

def segment_pattern_4_instance_4_goalIds : List Nat := [415, 416, 417, 418, 419, 420, 421, 422]
def segment_pattern_4_instance_4_stmt : Prop :=
  goal_415_stmt ∧ (goal_416_stmt ∧ (goal_417_stmt ∧ (goal_418_stmt ∧ (goal_419_stmt ∧ (goal_420_stmt ∧ (goal_421_stmt ∧ (goal_422_stmt)))))))

def segment_pattern_4_instance_5_goalIds : List Nat := [450, 451, 452, 453, 454, 455, 456, 457]
def segment_pattern_4_instance_5_stmt : Prop :=
  goal_450_stmt ∧ (goal_451_stmt ∧ (goal_452_stmt ∧ (goal_453_stmt ∧ (goal_454_stmt ∧ (goal_455_stmt ∧ (goal_456_stmt ∧ (goal_457_stmt)))))))

def segment_pattern_4_instance_6_goalIds : List Nat := [485, 486, 487, 488, 489, 490, 491, 492]
def segment_pattern_4_instance_6_stmt : Prop :=
  goal_485_stmt ∧ (goal_486_stmt ∧ (goal_487_stmt ∧ (goal_488_stmt ∧ (goal_489_stmt ∧ (goal_490_stmt ∧ (goal_491_stmt ∧ (goal_492_stmt)))))))

def segment_pattern_4_instance_7_goalIds : List Nat := [520, 521, 522, 523, 524, 525, 526, 527]
def segment_pattern_4_instance_7_stmt : Prop :=
  goal_520_stmt ∧ (goal_521_stmt ∧ (goal_522_stmt ∧ (goal_523_stmt ∧ (goal_524_stmt ∧ (goal_525_stmt ∧ (goal_526_stmt ∧ (goal_527_stmt)))))))

def segment_pattern_4_instance_8_goalIds : List Nat := [555, 556, 557, 558, 559, 560, 561, 562]
def segment_pattern_4_instance_8_stmt : Prop :=
  goal_555_stmt ∧ (goal_556_stmt ∧ (goal_557_stmt ∧ (goal_558_stmt ∧ (goal_559_stmt ∧ (goal_560_stmt ∧ (goal_561_stmt ∧ (goal_562_stmt)))))))

def segment_pattern_4_instance_9_goalIds : List Nat := [590, 591, 592, 593, 594, 595, 596, 597]
def segment_pattern_4_instance_9_stmt : Prop :=
  goal_590_stmt ∧ (goal_591_stmt ∧ (goal_592_stmt ∧ (goal_593_stmt ∧ (goal_594_stmt ∧ (goal_595_stmt ∧ (goal_596_stmt ∧ (goal_597_stmt)))))))

def segment_pattern_4_instance_10_goalIds : List Nat := [625, 626, 627, 628, 629, 630, 631, 632]
def segment_pattern_4_instance_10_stmt : Prop :=
  goal_625_stmt ∧ (goal_626_stmt ∧ (goal_627_stmt ∧ (goal_628_stmt ∧ (goal_629_stmt ∧ (goal_630_stmt ∧ (goal_631_stmt ∧ (goal_632_stmt)))))))

def segment_pattern_4_instance_11_goalIds : List Nat := [660, 661, 662, 663, 664, 665, 666, 667]
def segment_pattern_4_instance_11_stmt : Prop :=
  goal_660_stmt ∧ (goal_661_stmt ∧ (goal_662_stmt ∧ (goal_663_stmt ∧ (goal_664_stmt ∧ (goal_665_stmt ∧ (goal_666_stmt ∧ (goal_667_stmt)))))))

def segment_pattern_4_instance_12_goalIds : List Nat := [695, 696, 697, 698, 699, 700, 701, 702]
def segment_pattern_4_instance_12_stmt : Prop :=
  goal_695_stmt ∧ (goal_696_stmt ∧ (goal_697_stmt ∧ (goal_698_stmt ∧ (goal_699_stmt ∧ (goal_700_stmt ∧ (goal_701_stmt ∧ (goal_702_stmt)))))))

inductive segment_pattern_4_target : Prop → Prop
  | inst_1 : segment_pattern_4_target segment_pattern_4_instance_1_stmt
  | inst_2 : segment_pattern_4_target segment_pattern_4_instance_2_stmt
  | inst_3 : segment_pattern_4_target segment_pattern_4_instance_3_stmt
  | inst_4 : segment_pattern_4_target segment_pattern_4_instance_4_stmt
  | inst_5 : segment_pattern_4_target segment_pattern_4_instance_5_stmt
  | inst_6 : segment_pattern_4_target segment_pattern_4_instance_6_stmt
  | inst_7 : segment_pattern_4_target segment_pattern_4_instance_7_stmt
  | inst_8 : segment_pattern_4_target segment_pattern_4_instance_8_stmt
  | inst_9 : segment_pattern_4_target segment_pattern_4_instance_9_stmt
  | inst_10 : segment_pattern_4_target segment_pattern_4_instance_10_stmt
  | inst_11 : segment_pattern_4_target segment_pattern_4_instance_11_stmt
  | inst_12 : segment_pattern_4_target segment_pattern_4_instance_12_stmt

def segment_pattern_4_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_4_target target → target
theorem prove_segment_pattern_4 : segment_pattern_4_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

