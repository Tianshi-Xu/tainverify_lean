/- Auto-generated pattern proof file.
   Pattern: 220
   Hash: ffafe0f7e19884de
   Goals: 769, 853, 867, 881
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_220_goalIds : List Nat := [769, 853, 867, 881]
inductive pattern_220_target : Prop → Prop
  | goal_769 : pattern_220_target goal_769_stmt
  | goal_853 : pattern_220_target goal_853_stmt
  | goal_867 : pattern_220_target goal_867_stmt
  | goal_881 : pattern_220_target goal_881_stmt

def pattern_220_stmt : Prop :=
  ∀ {target : Prop}, pattern_220_target target → target
theorem prove_pattern_220 : pattern_220_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

