/- Auto-generated pattern proof file.
   Pattern: 78
   Hash: 6522a801ae6873b5
   Goals: 142
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_78_goalIds : List Nat := [142]
inductive pattern_78_target : Prop → Prop
  | goal_142 : pattern_78_target goal_142_stmt

def pattern_78_stmt : Prop :=
  ∀ {target : Prop}, pattern_78_target target → target
theorem prove_pattern_78 : pattern_78_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

