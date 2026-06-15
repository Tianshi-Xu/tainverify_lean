/- Auto-generated pattern proof file.
   Pattern: 46
   Hash: feaf0a8f2f7db76b
   Goals: 90
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_46_goalIds : List Nat := [90]
inductive pattern_46_target : Prop → Prop
  | goal_90 : pattern_46_target goal_90_stmt

def pattern_46_stmt : Prop :=
  ∀ {target : Prop}, pattern_46_target target → target
theorem prove_pattern_46 : pattern_46_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

