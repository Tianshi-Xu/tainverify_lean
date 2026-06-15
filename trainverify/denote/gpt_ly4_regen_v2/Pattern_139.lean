/- Auto-generated pattern proof file.
   Pattern: 139
   Hash: 937a885642ea4bfc
   Goals: 305
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_139_goalIds : List Nat := [305]
inductive pattern_139_target : Prop → Prop
  | goal_305 : pattern_139_target goal_305_stmt

def pattern_139_stmt : Prop :=
  ∀ {target : Prop}, pattern_139_target target → target
theorem prove_pattern_139 : pattern_139_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

