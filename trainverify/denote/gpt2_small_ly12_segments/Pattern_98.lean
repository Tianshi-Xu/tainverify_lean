/- Auto-generated pattern proof file.
   Pattern: 98
   Hash: 782f341d1dcbc271
   Goals: 319, 385, 387, 457, 459, 527, 529, 595, 597, 630, 658, 659, 665, 667, 728, 729, 746, 770, 772, 800, 802, 828, 830, 854, 856, 868, 882, 884
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_98_goalIds : List Nat := [319, 385, 387, 457, 459, 527, 529, 595, 597, 630, 658, 659, 665, 667, 728, 729, 746, 770, 772, 800, 802, 828, 830, 854, 856, 868, 882, 884]
inductive pattern_98_target : Prop → Prop
  | goal_319 : pattern_98_target goal_319_stmt
  | goal_385 : pattern_98_target goal_385_stmt
  | goal_387 : pattern_98_target goal_387_stmt
  | goal_457 : pattern_98_target goal_457_stmt
  | goal_459 : pattern_98_target goal_459_stmt
  | goal_527 : pattern_98_target goal_527_stmt
  | goal_529 : pattern_98_target goal_529_stmt
  | goal_595 : pattern_98_target goal_595_stmt
  | goal_597 : pattern_98_target goal_597_stmt
  | goal_630 : pattern_98_target goal_630_stmt
  | goal_658 : pattern_98_target goal_658_stmt
  | goal_659 : pattern_98_target goal_659_stmt
  | goal_665 : pattern_98_target goal_665_stmt
  | goal_667 : pattern_98_target goal_667_stmt
  | goal_728 : pattern_98_target goal_728_stmt
  | goal_729 : pattern_98_target goal_729_stmt
  | goal_746 : pattern_98_target goal_746_stmt
  | goal_770 : pattern_98_target goal_770_stmt
  | goal_772 : pattern_98_target goal_772_stmt
  | goal_800 : pattern_98_target goal_800_stmt
  | goal_802 : pattern_98_target goal_802_stmt
  | goal_828 : pattern_98_target goal_828_stmt
  | goal_830 : pattern_98_target goal_830_stmt
  | goal_854 : pattern_98_target goal_854_stmt
  | goal_856 : pattern_98_target goal_856_stmt
  | goal_868 : pattern_98_target goal_868_stmt
  | goal_882 : pattern_98_target goal_882_stmt
  | goal_884 : pattern_98_target goal_884_stmt

def pattern_98_stmt : Prop :=
  ∀ {target : Prop}, pattern_98_target target → target
theorem prove_pattern_98 : pattern_98_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

