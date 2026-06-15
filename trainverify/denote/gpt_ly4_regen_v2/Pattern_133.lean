/- Auto-generated pattern proof file.
   Pattern: 133
   Hash: aed5adffc490ef93
   Goals: 279
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_133_goalIds : List Nat := [279]
inductive pattern_133_target : Prop → Prop
  | goal_279 : pattern_133_target goal_279_stmt

def pattern_133_stmt : Prop :=
  ∀ {target : Prop}, pattern_133_target target → target
theorem prove_pattern_133 : pattern_133_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

