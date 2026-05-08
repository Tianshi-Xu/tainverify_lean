/- Auto-generated segment pattern proof file.
   Segment pattern: 7
   Goals per instance: 8
   Instances: 12
   Representative op scale: instances=12, goals/instance=8, ops/instance: SM=8, PM=54, ops=[OpName.BW_linear, OpName.ChunkPrim, OpName.AllGatherPrim, OpName.BW_add, OpName.AllReducePrim, OpName.BW_multiref, OpName.BW_layernorm, OpName.CROSS_DP_WRED]
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_7_instance_1_goalIds : List Nat := [334, 335, 336, 337, 338, 339, 340, 341]
def segment_pattern_7_instance_1_stmt : Prop :=
  goal_334_stmt ∧ (goal_335_stmt ∧ (goal_336_stmt ∧ (goal_337_stmt ∧ (goal_338_stmt ∧ (goal_339_stmt ∧ (goal_340_stmt ∧ (goal_341_stmt)))))))

def segment_pattern_7_instance_2_goalIds : List Nat := [369, 370, 371, 372, 373, 374, 375, 376]
def segment_pattern_7_instance_2_stmt : Prop :=
  goal_369_stmt ∧ (goal_370_stmt ∧ (goal_371_stmt ∧ (goal_372_stmt ∧ (goal_373_stmt ∧ (goal_374_stmt ∧ (goal_375_stmt ∧ (goal_376_stmt)))))))

def segment_pattern_7_instance_3_goalIds : List Nat := [404, 405, 406, 407, 408, 409, 410, 411]
def segment_pattern_7_instance_3_stmt : Prop :=
  goal_404_stmt ∧ (goal_405_stmt ∧ (goal_406_stmt ∧ (goal_407_stmt ∧ (goal_408_stmt ∧ (goal_409_stmt ∧ (goal_410_stmt ∧ (goal_411_stmt)))))))

def segment_pattern_7_instance_4_goalIds : List Nat := [439, 440, 441, 442, 443, 444, 445, 446]
def segment_pattern_7_instance_4_stmt : Prop :=
  goal_439_stmt ∧ (goal_440_stmt ∧ (goal_441_stmt ∧ (goal_442_stmt ∧ (goal_443_stmt ∧ (goal_444_stmt ∧ (goal_445_stmt ∧ (goal_446_stmt)))))))

def segment_pattern_7_instance_5_goalIds : List Nat := [474, 475, 476, 477, 478, 479, 480, 481]
def segment_pattern_7_instance_5_stmt : Prop :=
  goal_474_stmt ∧ (goal_475_stmt ∧ (goal_476_stmt ∧ (goal_477_stmt ∧ (goal_478_stmt ∧ (goal_479_stmt ∧ (goal_480_stmt ∧ (goal_481_stmt)))))))

def segment_pattern_7_instance_6_goalIds : List Nat := [509, 510, 511, 512, 513, 514, 515, 516]
def segment_pattern_7_instance_6_stmt : Prop :=
  goal_509_stmt ∧ (goal_510_stmt ∧ (goal_511_stmt ∧ (goal_512_stmt ∧ (goal_513_stmt ∧ (goal_514_stmt ∧ (goal_515_stmt ∧ (goal_516_stmt)))))))

def segment_pattern_7_instance_7_goalIds : List Nat := [544, 545, 546, 547, 548, 549, 550, 551]
def segment_pattern_7_instance_7_stmt : Prop :=
  goal_544_stmt ∧ (goal_545_stmt ∧ (goal_546_stmt ∧ (goal_547_stmt ∧ (goal_548_stmt ∧ (goal_549_stmt ∧ (goal_550_stmt ∧ (goal_551_stmt)))))))

def segment_pattern_7_instance_8_goalIds : List Nat := [579, 580, 581, 582, 583, 584, 585, 586]
def segment_pattern_7_instance_8_stmt : Prop :=
  goal_579_stmt ∧ (goal_580_stmt ∧ (goal_581_stmt ∧ (goal_582_stmt ∧ (goal_583_stmt ∧ (goal_584_stmt ∧ (goal_585_stmt ∧ (goal_586_stmt)))))))

def segment_pattern_7_instance_9_goalIds : List Nat := [614, 615, 616, 617, 618, 619, 620, 621]
def segment_pattern_7_instance_9_stmt : Prop :=
  goal_614_stmt ∧ (goal_615_stmt ∧ (goal_616_stmt ∧ (goal_617_stmt ∧ (goal_618_stmt ∧ (goal_619_stmt ∧ (goal_620_stmt ∧ (goal_621_stmt)))))))

def segment_pattern_7_instance_10_goalIds : List Nat := [649, 650, 651, 652, 653, 654, 655, 656]
def segment_pattern_7_instance_10_stmt : Prop :=
  goal_649_stmt ∧ (goal_650_stmt ∧ (goal_651_stmt ∧ (goal_652_stmt ∧ (goal_653_stmt ∧ (goal_654_stmt ∧ (goal_655_stmt ∧ (goal_656_stmt)))))))

def segment_pattern_7_instance_11_goalIds : List Nat := [684, 685, 686, 687, 688, 689, 690, 691]
def segment_pattern_7_instance_11_stmt : Prop :=
  goal_684_stmt ∧ (goal_685_stmt ∧ (goal_686_stmt ∧ (goal_687_stmt ∧ (goal_688_stmt ∧ (goal_689_stmt ∧ (goal_690_stmt ∧ (goal_691_stmt)))))))

def segment_pattern_7_instance_12_goalIds : List Nat := [719, 720, 721, 722, 723, 724, 725, 726]
def segment_pattern_7_instance_12_stmt : Prop :=
  goal_719_stmt ∧ (goal_720_stmt ∧ (goal_721_stmt ∧ (goal_722_stmt ∧ (goal_723_stmt ∧ (goal_724_stmt ∧ (goal_725_stmt ∧ (goal_726_stmt)))))))

inductive segment_pattern_7_target : Prop → Prop
  | inst_1 : segment_pattern_7_target segment_pattern_7_instance_1_stmt
  | inst_2 : segment_pattern_7_target segment_pattern_7_instance_2_stmt
  | inst_3 : segment_pattern_7_target segment_pattern_7_instance_3_stmt
  | inst_4 : segment_pattern_7_target segment_pattern_7_instance_4_stmt
  | inst_5 : segment_pattern_7_target segment_pattern_7_instance_5_stmt
  | inst_6 : segment_pattern_7_target segment_pattern_7_instance_6_stmt
  | inst_7 : segment_pattern_7_target segment_pattern_7_instance_7_stmt
  | inst_8 : segment_pattern_7_target segment_pattern_7_instance_8_stmt
  | inst_9 : segment_pattern_7_target segment_pattern_7_instance_9_stmt
  | inst_10 : segment_pattern_7_target segment_pattern_7_instance_10_stmt
  | inst_11 : segment_pattern_7_target segment_pattern_7_instance_11_stmt
  | inst_12 : segment_pattern_7_target segment_pattern_7_instance_12_stmt

def segment_pattern_7_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_7_target target → target
theorem prove_segment_pattern_7 : segment_pattern_7_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

