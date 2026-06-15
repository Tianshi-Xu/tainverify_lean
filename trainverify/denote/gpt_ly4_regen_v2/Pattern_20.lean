/- Auto-generated pattern proof file.
   Pattern: 20
   Hash: 6413053af5c9da02
   Goals: 24
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_20_goalIds : List Nat := [24]
inductive pattern_20_target : Prop → Prop
  | goal_24 : pattern_20_target goal_24_stmt

def pattern_20_stmt : Prop :=
  ∀ {target : Prop}, pattern_20_target target → target
theorem prove_pattern_20 : pattern_20_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

