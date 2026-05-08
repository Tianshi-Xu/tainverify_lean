/- Auto-generated pattern proof file.
   Pattern: 216
   Hash: 05d53b83208ff068
   Goals: 756, 760, 784, 786, 798, 812, 816, 840, 842, 870, 886, 896, 898
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_216_goalIds : List Nat := [756, 760, 784, 786, 798, 812, 816, 840, 842, 870, 886, 896, 898]
inductive pattern_216_target : Prop → Prop
  | goal_756 : pattern_216_target goal_756_stmt
  | goal_760 : pattern_216_target goal_760_stmt
  | goal_784 : pattern_216_target goal_784_stmt
  | goal_786 : pattern_216_target goal_786_stmt
  | goal_798 : pattern_216_target goal_798_stmt
  | goal_812 : pattern_216_target goal_812_stmt
  | goal_816 : pattern_216_target goal_816_stmt
  | goal_840 : pattern_216_target goal_840_stmt
  | goal_842 : pattern_216_target goal_842_stmt
  | goal_870 : pattern_216_target goal_870_stmt
  | goal_886 : pattern_216_target goal_886_stmt
  | goal_896 : pattern_216_target goal_896_stmt
  | goal_898 : pattern_216_target goal_898_stmt

def pattern_216_stmt : Prop :=
  ∀ {target : Prop}, pattern_216_target target → target
theorem prove_pattern_216 : pattern_216_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

