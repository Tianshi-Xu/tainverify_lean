/- Auto-generated pattern proof file.
   Pattern: 117
   Hash: 0ee7e554cd30a506
   Goals: 231
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_117_goalIds : List Nat := [231]
inductive pattern_117_target : Prop → Prop
  | goal_231 : pattern_117_target goal_231_stmt

def pattern_117_stmt : Prop :=
  ∀ {target : Prop}, pattern_117_target target → target
theorem prove_pattern_117 : pattern_117_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

