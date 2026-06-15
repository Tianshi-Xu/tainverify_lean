/- Auto-generated pattern proof file.
   Pattern: 122
   Hash: f4996e99209b830a
   Goals: 237
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_122_goalIds : List Nat := [237]
inductive pattern_122_target : Prop → Prop
  | goal_237 : pattern_122_target goal_237_stmt

def pattern_122_stmt : Prop :=
  ∀ {target : Prop}, pattern_122_target target → target
theorem prove_pattern_122 : pattern_122_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

