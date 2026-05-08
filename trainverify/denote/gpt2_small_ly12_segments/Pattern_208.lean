/- Auto-generated pattern proof file.
   Pattern: 208
   Hash: 9df962180fe72704
   Goals: 738, 748, 752, 762, 766, 776, 780, 790, 794, 804, 808, 818, 822, 832, 836, 846, 850, 860, 864, 874, 878, 888, 892, 902
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_208_goalIds : List Nat := [738, 748, 752, 762, 766, 776, 780, 790, 794, 804, 808, 818, 822, 832, 836, 846, 850, 860, 864, 874, 878, 888, 892, 902]
inductive pattern_208_target : Prop → Prop
  | goal_738 : pattern_208_target goal_738_stmt
  | goal_748 : pattern_208_target goal_748_stmt
  | goal_752 : pattern_208_target goal_752_stmt
  | goal_762 : pattern_208_target goal_762_stmt
  | goal_766 : pattern_208_target goal_766_stmt
  | goal_776 : pattern_208_target goal_776_stmt
  | goal_780 : pattern_208_target goal_780_stmt
  | goal_790 : pattern_208_target goal_790_stmt
  | goal_794 : pattern_208_target goal_794_stmt
  | goal_804 : pattern_208_target goal_804_stmt
  | goal_808 : pattern_208_target goal_808_stmt
  | goal_818 : pattern_208_target goal_818_stmt
  | goal_822 : pattern_208_target goal_822_stmt
  | goal_832 : pattern_208_target goal_832_stmt
  | goal_836 : pattern_208_target goal_836_stmt
  | goal_846 : pattern_208_target goal_846_stmt
  | goal_850 : pattern_208_target goal_850_stmt
  | goal_860 : pattern_208_target goal_860_stmt
  | goal_864 : pattern_208_target goal_864_stmt
  | goal_874 : pattern_208_target goal_874_stmt
  | goal_878 : pattern_208_target goal_878_stmt
  | goal_888 : pattern_208_target goal_888_stmt
  | goal_892 : pattern_208_target goal_892_stmt
  | goal_902 : pattern_208_target goal_902_stmt

def pattern_208_stmt : Prop :=
  ∀ {target : Prop}, pattern_208_target target → target
theorem prove_pattern_208 : pattern_208_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

