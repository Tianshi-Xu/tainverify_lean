/- Auto-generated pattern proof file.
   Pattern: 32
   Hash: 751f5da041372c5f
   Goals: 46
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_32_goalIds : List Nat := [46]
inductive pattern_32_target : Prop → Prop
  | goal_46 : pattern_32_target goal_46_stmt

def pattern_32_stmt : Prop :=
  ∀ {target : Prop}, pattern_32_target target → target
theorem prove_pattern_32 : pattern_32_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

