/- Auto-generated segment pattern proof file.
   Segment pattern: 5
   Goals per instance: 8
   Instances: 12
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_5_instance_1_goalIds : List Nat := [318, 319, 320, 321, 322, 323, 324, 325]
def segment_pattern_5_instance_1_stmt : Prop :=
  goal_318_stmt ∧ (goal_319_stmt ∧ (goal_320_stmt ∧ (goal_321_stmt ∧ (goal_322_stmt ∧ (goal_323_stmt ∧ (goal_324_stmt ∧ (goal_325_stmt)))))))

def segment_pattern_5_instance_2_goalIds : List Nat := [353, 354, 355, 356, 357, 358, 359, 360]
def segment_pattern_5_instance_2_stmt : Prop :=
  goal_353_stmt ∧ (goal_354_stmt ∧ (goal_355_stmt ∧ (goal_356_stmt ∧ (goal_357_stmt ∧ (goal_358_stmt ∧ (goal_359_stmt ∧ (goal_360_stmt)))))))

def segment_pattern_5_instance_3_goalIds : List Nat := [388, 389, 390, 391, 392, 393, 394, 395]
def segment_pattern_5_instance_3_stmt : Prop :=
  goal_388_stmt ∧ (goal_389_stmt ∧ (goal_390_stmt ∧ (goal_391_stmt ∧ (goal_392_stmt ∧ (goal_393_stmt ∧ (goal_394_stmt ∧ (goal_395_stmt)))))))

def segment_pattern_5_instance_4_goalIds : List Nat := [423, 424, 425, 426, 427, 428, 429, 430]
def segment_pattern_5_instance_4_stmt : Prop :=
  goal_423_stmt ∧ (goal_424_stmt ∧ (goal_425_stmt ∧ (goal_426_stmt ∧ (goal_427_stmt ∧ (goal_428_stmt ∧ (goal_429_stmt ∧ (goal_430_stmt)))))))

def segment_pattern_5_instance_5_goalIds : List Nat := [458, 459, 460, 461, 462, 463, 464, 465]
def segment_pattern_5_instance_5_stmt : Prop :=
  goal_458_stmt ∧ (goal_459_stmt ∧ (goal_460_stmt ∧ (goal_461_stmt ∧ (goal_462_stmt ∧ (goal_463_stmt ∧ (goal_464_stmt ∧ (goal_465_stmt)))))))

def segment_pattern_5_instance_6_goalIds : List Nat := [493, 494, 495, 496, 497, 498, 499, 500]
def segment_pattern_5_instance_6_stmt : Prop :=
  goal_493_stmt ∧ (goal_494_stmt ∧ (goal_495_stmt ∧ (goal_496_stmt ∧ (goal_497_stmt ∧ (goal_498_stmt ∧ (goal_499_stmt ∧ (goal_500_stmt)))))))

def segment_pattern_5_instance_7_goalIds : List Nat := [528, 529, 530, 531, 532, 533, 534, 535]
def segment_pattern_5_instance_7_stmt : Prop :=
  goal_528_stmt ∧ (goal_529_stmt ∧ (goal_530_stmt ∧ (goal_531_stmt ∧ (goal_532_stmt ∧ (goal_533_stmt ∧ (goal_534_stmt ∧ (goal_535_stmt)))))))

def segment_pattern_5_instance_8_goalIds : List Nat := [563, 564, 565, 566, 567, 568, 569, 570]
def segment_pattern_5_instance_8_stmt : Prop :=
  goal_563_stmt ∧ (goal_564_stmt ∧ (goal_565_stmt ∧ (goal_566_stmt ∧ (goal_567_stmt ∧ (goal_568_stmt ∧ (goal_569_stmt ∧ (goal_570_stmt)))))))

def segment_pattern_5_instance_9_goalIds : List Nat := [598, 599, 600, 601, 602, 603, 604, 605]
def segment_pattern_5_instance_9_stmt : Prop :=
  goal_598_stmt ∧ (goal_599_stmt ∧ (goal_600_stmt ∧ (goal_601_stmt ∧ (goal_602_stmt ∧ (goal_603_stmt ∧ (goal_604_stmt ∧ (goal_605_stmt)))))))

def segment_pattern_5_instance_10_goalIds : List Nat := [633, 634, 635, 636, 637, 638, 639, 640]
def segment_pattern_5_instance_10_stmt : Prop :=
  goal_633_stmt ∧ (goal_634_stmt ∧ (goal_635_stmt ∧ (goal_636_stmt ∧ (goal_637_stmt ∧ (goal_638_stmt ∧ (goal_639_stmt ∧ (goal_640_stmt)))))))

def segment_pattern_5_instance_11_goalIds : List Nat := [668, 669, 670, 671, 672, 673, 674, 675]
def segment_pattern_5_instance_11_stmt : Prop :=
  goal_668_stmt ∧ (goal_669_stmt ∧ (goal_670_stmt ∧ (goal_671_stmt ∧ (goal_672_stmt ∧ (goal_673_stmt ∧ (goal_674_stmt ∧ (goal_675_stmt)))))))

def segment_pattern_5_instance_12_goalIds : List Nat := [703, 704, 705, 706, 707, 708, 709, 710]
def segment_pattern_5_instance_12_stmt : Prop :=
  goal_703_stmt ∧ (goal_704_stmt ∧ (goal_705_stmt ∧ (goal_706_stmt ∧ (goal_707_stmt ∧ (goal_708_stmt ∧ (goal_709_stmt ∧ (goal_710_stmt)))))))

inductive segment_pattern_5_target : Prop → Prop
  | inst_1 : segment_pattern_5_target segment_pattern_5_instance_1_stmt
  | inst_2 : segment_pattern_5_target segment_pattern_5_instance_2_stmt
  | inst_3 : segment_pattern_5_target segment_pattern_5_instance_3_stmt
  | inst_4 : segment_pattern_5_target segment_pattern_5_instance_4_stmt
  | inst_5 : segment_pattern_5_target segment_pattern_5_instance_5_stmt
  | inst_6 : segment_pattern_5_target segment_pattern_5_instance_6_stmt
  | inst_7 : segment_pattern_5_target segment_pattern_5_instance_7_stmt
  | inst_8 : segment_pattern_5_target segment_pattern_5_instance_8_stmt
  | inst_9 : segment_pattern_5_target segment_pattern_5_instance_9_stmt
  | inst_10 : segment_pattern_5_target segment_pattern_5_instance_10_stmt
  | inst_11 : segment_pattern_5_target segment_pattern_5_instance_11_stmt
  | inst_12 : segment_pattern_5_target segment_pattern_5_instance_12_stmt

def segment_pattern_5_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_5_target target → target
theorem prove_segment_pattern_5 : segment_pattern_5_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

