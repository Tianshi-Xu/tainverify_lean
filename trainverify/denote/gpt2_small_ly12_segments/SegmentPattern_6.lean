/- Auto-generated segment pattern proof file.
   Segment pattern: 6
   Goals per instance: 8
   Instances: 12
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_6_instance_1_goalIds : List Nat := [326, 327, 328, 329, 330, 331, 332, 333]
def segment_pattern_6_instance_1_stmt : Prop :=
  goal_326_stmt ∧ (goal_327_stmt ∧ (goal_328_stmt ∧ (goal_329_stmt ∧ (goal_330_stmt ∧ (goal_331_stmt ∧ (goal_332_stmt ∧ (goal_333_stmt)))))))

def segment_pattern_6_instance_2_goalIds : List Nat := [361, 362, 363, 364, 365, 366, 367, 368]
def segment_pattern_6_instance_2_stmt : Prop :=
  goal_361_stmt ∧ (goal_362_stmt ∧ (goal_363_stmt ∧ (goal_364_stmt ∧ (goal_365_stmt ∧ (goal_366_stmt ∧ (goal_367_stmt ∧ (goal_368_stmt)))))))

def segment_pattern_6_instance_3_goalIds : List Nat := [396, 397, 398, 399, 400, 401, 402, 403]
def segment_pattern_6_instance_3_stmt : Prop :=
  goal_396_stmt ∧ (goal_397_stmt ∧ (goal_398_stmt ∧ (goal_399_stmt ∧ (goal_400_stmt ∧ (goal_401_stmt ∧ (goal_402_stmt ∧ (goal_403_stmt)))))))

def segment_pattern_6_instance_4_goalIds : List Nat := [431, 432, 433, 434, 435, 436, 437, 438]
def segment_pattern_6_instance_4_stmt : Prop :=
  goal_431_stmt ∧ (goal_432_stmt ∧ (goal_433_stmt ∧ (goal_434_stmt ∧ (goal_435_stmt ∧ (goal_436_stmt ∧ (goal_437_stmt ∧ (goal_438_stmt)))))))

def segment_pattern_6_instance_5_goalIds : List Nat := [466, 467, 468, 469, 470, 471, 472, 473]
def segment_pattern_6_instance_5_stmt : Prop :=
  goal_466_stmt ∧ (goal_467_stmt ∧ (goal_468_stmt ∧ (goal_469_stmt ∧ (goal_470_stmt ∧ (goal_471_stmt ∧ (goal_472_stmt ∧ (goal_473_stmt)))))))

def segment_pattern_6_instance_6_goalIds : List Nat := [501, 502, 503, 504, 505, 506, 507, 508]
def segment_pattern_6_instance_6_stmt : Prop :=
  goal_501_stmt ∧ (goal_502_stmt ∧ (goal_503_stmt ∧ (goal_504_stmt ∧ (goal_505_stmt ∧ (goal_506_stmt ∧ (goal_507_stmt ∧ (goal_508_stmt)))))))

def segment_pattern_6_instance_7_goalIds : List Nat := [536, 537, 538, 539, 540, 541, 542, 543]
def segment_pattern_6_instance_7_stmt : Prop :=
  goal_536_stmt ∧ (goal_537_stmt ∧ (goal_538_stmt ∧ (goal_539_stmt ∧ (goal_540_stmt ∧ (goal_541_stmt ∧ (goal_542_stmt ∧ (goal_543_stmt)))))))

def segment_pattern_6_instance_8_goalIds : List Nat := [571, 572, 573, 574, 575, 576, 577, 578]
def segment_pattern_6_instance_8_stmt : Prop :=
  goal_571_stmt ∧ (goal_572_stmt ∧ (goal_573_stmt ∧ (goal_574_stmt ∧ (goal_575_stmt ∧ (goal_576_stmt ∧ (goal_577_stmt ∧ (goal_578_stmt)))))))

def segment_pattern_6_instance_9_goalIds : List Nat := [606, 607, 608, 609, 610, 611, 612, 613]
def segment_pattern_6_instance_9_stmt : Prop :=
  goal_606_stmt ∧ (goal_607_stmt ∧ (goal_608_stmt ∧ (goal_609_stmt ∧ (goal_610_stmt ∧ (goal_611_stmt ∧ (goal_612_stmt ∧ (goal_613_stmt)))))))

def segment_pattern_6_instance_10_goalIds : List Nat := [641, 642, 643, 644, 645, 646, 647, 648]
def segment_pattern_6_instance_10_stmt : Prop :=
  goal_641_stmt ∧ (goal_642_stmt ∧ (goal_643_stmt ∧ (goal_644_stmt ∧ (goal_645_stmt ∧ (goal_646_stmt ∧ (goal_647_stmt ∧ (goal_648_stmt)))))))

def segment_pattern_6_instance_11_goalIds : List Nat := [676, 677, 678, 679, 680, 681, 682, 683]
def segment_pattern_6_instance_11_stmt : Prop :=
  goal_676_stmt ∧ (goal_677_stmt ∧ (goal_678_stmt ∧ (goal_679_stmt ∧ (goal_680_stmt ∧ (goal_681_stmt ∧ (goal_682_stmt ∧ (goal_683_stmt)))))))

def segment_pattern_6_instance_12_goalIds : List Nat := [711, 712, 713, 714, 715, 716, 717, 718]
def segment_pattern_6_instance_12_stmt : Prop :=
  goal_711_stmt ∧ (goal_712_stmt ∧ (goal_713_stmt ∧ (goal_714_stmt ∧ (goal_715_stmt ∧ (goal_716_stmt ∧ (goal_717_stmt ∧ (goal_718_stmt)))))))

inductive segment_pattern_6_target : Prop → Prop
  | inst_1 : segment_pattern_6_target segment_pattern_6_instance_1_stmt
  | inst_2 : segment_pattern_6_target segment_pattern_6_instance_2_stmt
  | inst_3 : segment_pattern_6_target segment_pattern_6_instance_3_stmt
  | inst_4 : segment_pattern_6_target segment_pattern_6_instance_4_stmt
  | inst_5 : segment_pattern_6_target segment_pattern_6_instance_5_stmt
  | inst_6 : segment_pattern_6_target segment_pattern_6_instance_6_stmt
  | inst_7 : segment_pattern_6_target segment_pattern_6_instance_7_stmt
  | inst_8 : segment_pattern_6_target segment_pattern_6_instance_8_stmt
  | inst_9 : segment_pattern_6_target segment_pattern_6_instance_9_stmt
  | inst_10 : segment_pattern_6_target segment_pattern_6_instance_10_stmt
  | inst_11 : segment_pattern_6_target segment_pattern_6_instance_11_stmt
  | inst_12 : segment_pattern_6_target segment_pattern_6_instance_12_stmt

def segment_pattern_6_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_6_target target → target
theorem prove_segment_pattern_6 : segment_pattern_6_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

