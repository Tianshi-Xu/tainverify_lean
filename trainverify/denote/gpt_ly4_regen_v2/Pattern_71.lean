/- Auto-generated pattern proof file.
   Pattern: 71
   Hash: 60b2b79ebfc5c86d
   Goals: 131
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_71_goalIds : List Nat := [131]
inductive pattern_71_target : Prop → Prop
  | goal_131 : pattern_71_target goal_131_stmt

def pattern_71_stmt : Prop :=
  ∀ {target : Prop}, pattern_71_target target → target
theorem prove_pattern_71 : pattern_71_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

