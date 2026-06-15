/- Auto-generated pattern proof file.
   Pattern: 41
   Hash: 71f8f15f7757f99e
   Goals: 71
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_41_goalIds : List Nat := [71]
inductive pattern_41_target : Prop → Prop
  | goal_71 : pattern_41_target goal_71_stmt

def pattern_41_stmt : Prop :=
  ∀ {target : Prop}, pattern_41_target target → target
theorem prove_pattern_41 : pattern_41_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

