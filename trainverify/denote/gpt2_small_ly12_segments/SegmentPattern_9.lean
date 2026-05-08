/- Auto-generated segment pattern proof file.
   Segment pattern: 9
   Goals per instance: 8
   Instances: 12
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSegmentPatterns

def segment_pattern_9_instance_1_goalIds : List Nat := [737, 738, 739, 740, 741, 742, 743, 744]
def segment_pattern_9_instance_1_stmt : Prop :=
  goal_737_stmt ∧ (goal_738_stmt ∧ (goal_739_stmt ∧ (goal_740_stmt ∧ (goal_741_stmt ∧ (goal_742_stmt ∧ (goal_743_stmt ∧ (goal_744_stmt)))))))

def segment_pattern_9_instance_2_goalIds : List Nat := [751, 752, 753, 754, 755, 756, 757, 758]
def segment_pattern_9_instance_2_stmt : Prop :=
  goal_751_stmt ∧ (goal_752_stmt ∧ (goal_753_stmt ∧ (goal_754_stmt ∧ (goal_755_stmt ∧ (goal_756_stmt ∧ (goal_757_stmt ∧ (goal_758_stmt)))))))

def segment_pattern_9_instance_3_goalIds : List Nat := [765, 766, 767, 768, 769, 770, 771, 772]
def segment_pattern_9_instance_3_stmt : Prop :=
  goal_765_stmt ∧ (goal_766_stmt ∧ (goal_767_stmt ∧ (goal_768_stmt ∧ (goal_769_stmt ∧ (goal_770_stmt ∧ (goal_771_stmt ∧ (goal_772_stmt)))))))

def segment_pattern_9_instance_4_goalIds : List Nat := [779, 780, 781, 782, 783, 784, 785, 786]
def segment_pattern_9_instance_4_stmt : Prop :=
  goal_779_stmt ∧ (goal_780_stmt ∧ (goal_781_stmt ∧ (goal_782_stmt ∧ (goal_783_stmt ∧ (goal_784_stmt ∧ (goal_785_stmt ∧ (goal_786_stmt)))))))

def segment_pattern_9_instance_5_goalIds : List Nat := [793, 794, 795, 796, 797, 798, 799, 800]
def segment_pattern_9_instance_5_stmt : Prop :=
  goal_793_stmt ∧ (goal_794_stmt ∧ (goal_795_stmt ∧ (goal_796_stmt ∧ (goal_797_stmt ∧ (goal_798_stmt ∧ (goal_799_stmt ∧ (goal_800_stmt)))))))

def segment_pattern_9_instance_6_goalIds : List Nat := [807, 808, 809, 810, 811, 812, 813, 814]
def segment_pattern_9_instance_6_stmt : Prop :=
  goal_807_stmt ∧ (goal_808_stmt ∧ (goal_809_stmt ∧ (goal_810_stmt ∧ (goal_811_stmt ∧ (goal_812_stmt ∧ (goal_813_stmt ∧ (goal_814_stmt)))))))

def segment_pattern_9_instance_7_goalIds : List Nat := [821, 822, 823, 824, 825, 826, 827, 828]
def segment_pattern_9_instance_7_stmt : Prop :=
  goal_821_stmt ∧ (goal_822_stmt ∧ (goal_823_stmt ∧ (goal_824_stmt ∧ (goal_825_stmt ∧ (goal_826_stmt ∧ (goal_827_stmt ∧ (goal_828_stmt)))))))

def segment_pattern_9_instance_8_goalIds : List Nat := [835, 836, 837, 838, 839, 840, 841, 842]
def segment_pattern_9_instance_8_stmt : Prop :=
  goal_835_stmt ∧ (goal_836_stmt ∧ (goal_837_stmt ∧ (goal_838_stmt ∧ (goal_839_stmt ∧ (goal_840_stmt ∧ (goal_841_stmt ∧ (goal_842_stmt)))))))

def segment_pattern_9_instance_9_goalIds : List Nat := [849, 850, 851, 852, 853, 854, 855, 856]
def segment_pattern_9_instance_9_stmt : Prop :=
  goal_849_stmt ∧ (goal_850_stmt ∧ (goal_851_stmt ∧ (goal_852_stmt ∧ (goal_853_stmt ∧ (goal_854_stmt ∧ (goal_855_stmt ∧ (goal_856_stmt)))))))

def segment_pattern_9_instance_10_goalIds : List Nat := [863, 864, 865, 866, 867, 868, 869, 870]
def segment_pattern_9_instance_10_stmt : Prop :=
  goal_863_stmt ∧ (goal_864_stmt ∧ (goal_865_stmt ∧ (goal_866_stmt ∧ (goal_867_stmt ∧ (goal_868_stmt ∧ (goal_869_stmt ∧ (goal_870_stmt)))))))

def segment_pattern_9_instance_11_goalIds : List Nat := [877, 878, 879, 880, 881, 882, 883, 884]
def segment_pattern_9_instance_11_stmt : Prop :=
  goal_877_stmt ∧ (goal_878_stmt ∧ (goal_879_stmt ∧ (goal_880_stmt ∧ (goal_881_stmt ∧ (goal_882_stmt ∧ (goal_883_stmt ∧ (goal_884_stmt)))))))

def segment_pattern_9_instance_12_goalIds : List Nat := [891, 892, 893, 894, 895, 896, 897, 898]
def segment_pattern_9_instance_12_stmt : Prop :=
  goal_891_stmt ∧ (goal_892_stmt ∧ (goal_893_stmt ∧ (goal_894_stmt ∧ (goal_895_stmt ∧ (goal_896_stmt ∧ (goal_897_stmt ∧ (goal_898_stmt)))))))

inductive segment_pattern_9_target : Prop → Prop
  | inst_1 : segment_pattern_9_target segment_pattern_9_instance_1_stmt
  | inst_2 : segment_pattern_9_target segment_pattern_9_instance_2_stmt
  | inst_3 : segment_pattern_9_target segment_pattern_9_instance_3_stmt
  | inst_4 : segment_pattern_9_target segment_pattern_9_instance_4_stmt
  | inst_5 : segment_pattern_9_target segment_pattern_9_instance_5_stmt
  | inst_6 : segment_pattern_9_target segment_pattern_9_instance_6_stmt
  | inst_7 : segment_pattern_9_target segment_pattern_9_instance_7_stmt
  | inst_8 : segment_pattern_9_target segment_pattern_9_instance_8_stmt
  | inst_9 : segment_pattern_9_target segment_pattern_9_instance_9_stmt
  | inst_10 : segment_pattern_9_target segment_pattern_9_instance_10_stmt
  | inst_11 : segment_pattern_9_target segment_pattern_9_instance_11_stmt
  | inst_12 : segment_pattern_9_target segment_pattern_9_instance_12_stmt

def segment_pattern_9_stmt : Prop :=
  ∀ {target : Prop}, segment_pattern_9_target target → target
theorem prove_segment_pattern_9 : segment_pattern_9_stmt := by
  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.
  sorry

end TrainVerify.Denote.GeneratedSegmentPatterns

