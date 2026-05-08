/- Auto-generated pattern proof file.
   Pattern: 215
   Hash: 728f1d55e9e12045
   Goals: 755, 759, 783, 785, 797, 811, 815, 839, 841, 869, 885, 895, 897
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_215_goalIds : List Nat := [755, 759, 783, 785, 797, 811, 815, 839, 841, 869, 885, 895, 897]
inductive pattern_215_target : Prop → Prop
  | goal_755 : pattern_215_target goal_755_stmt
  | goal_759 : pattern_215_target goal_759_stmt
  | goal_783 : pattern_215_target goal_783_stmt
  | goal_785 : pattern_215_target goal_785_stmt
  | goal_797 : pattern_215_target goal_797_stmt
  | goal_811 : pattern_215_target goal_811_stmt
  | goal_815 : pattern_215_target goal_815_stmt
  | goal_839 : pattern_215_target goal_839_stmt
  | goal_841 : pattern_215_target goal_841_stmt
  | goal_869 : pattern_215_target goal_869_stmt
  | goal_885 : pattern_215_target goal_885_stmt
  | goal_895 : pattern_215_target goal_895_stmt
  | goal_897 : pattern_215_target goal_897_stmt

def pattern_215_stmt : Prop :=
  ∀ {target : Prop}, pattern_215_target target → target
theorem prove_pattern_215 : pattern_215_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

