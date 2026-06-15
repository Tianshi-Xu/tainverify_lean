/- Auto-generated pattern proof file.
   Pattern: 84
   Hash: bb170cc2ef1a2985
   Goals: 156, 195, 230
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_84_goalIds : List Nat := [156, 195, 230]
inductive pattern_84_target : Prop → Prop
  | goal_156 : pattern_84_target goal_156_stmt
  | goal_195 : pattern_84_target goal_195_stmt
  | goal_230 : pattern_84_target goal_230_stmt

def pattern_84_stmt : Prop :=
  ∀ {target : Prop}, pattern_84_target target → target
theorem prove_pattern_84 : pattern_84_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

