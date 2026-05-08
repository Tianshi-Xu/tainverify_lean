/- Auto-generated pattern proof file.
   Pattern: 207
   Hash: f9e77ec7d2a424da
   Goals: 737, 739, 747, 749, 751, 753, 761, 767, 777, 781, 791, 803, 817, 823, 835, 837, 845, 847, 849, 863, 877, 879, 887, 889, 891, 893, 901
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_207_goalIds : List Nat := [737, 739, 747, 749, 751, 753, 761, 767, 777, 781, 791, 803, 817, 823, 835, 837, 845, 847, 849, 863, 877, 879, 887, 889, 891, 893, 901]
inductive pattern_207_target : Prop → Prop
  | goal_737 : pattern_207_target goal_737_stmt
  | goal_739 : pattern_207_target goal_739_stmt
  | goal_747 : pattern_207_target goal_747_stmt
  | goal_749 : pattern_207_target goal_749_stmt
  | goal_751 : pattern_207_target goal_751_stmt
  | goal_753 : pattern_207_target goal_753_stmt
  | goal_761 : pattern_207_target goal_761_stmt
  | goal_767 : pattern_207_target goal_767_stmt
  | goal_777 : pattern_207_target goal_777_stmt
  | goal_781 : pattern_207_target goal_781_stmt
  | goal_791 : pattern_207_target goal_791_stmt
  | goal_803 : pattern_207_target goal_803_stmt
  | goal_817 : pattern_207_target goal_817_stmt
  | goal_823 : pattern_207_target goal_823_stmt
  | goal_835 : pattern_207_target goal_835_stmt
  | goal_837 : pattern_207_target goal_837_stmt
  | goal_845 : pattern_207_target goal_845_stmt
  | goal_847 : pattern_207_target goal_847_stmt
  | goal_849 : pattern_207_target goal_849_stmt
  | goal_863 : pattern_207_target goal_863_stmt
  | goal_877 : pattern_207_target goal_877_stmt
  | goal_879 : pattern_207_target goal_879_stmt
  | goal_887 : pattern_207_target goal_887_stmt
  | goal_889 : pattern_207_target goal_889_stmt
  | goal_891 : pattern_207_target goal_891_stmt
  | goal_893 : pattern_207_target goal_893_stmt
  | goal_901 : pattern_207_target goal_901_stmt

def pattern_207_stmt : Prop :=
  ∀ {target : Prop}, pattern_207_target target → target
theorem prove_pattern_207 : pattern_207_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

