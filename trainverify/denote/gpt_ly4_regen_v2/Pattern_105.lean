/- Auto-generated pattern proof file.
   Pattern: 105
   Hash: e4b0e5b291300976
   Goals: 200
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_105_goalIds : List Nat := [200]
inductive pattern_105_target : Prop → Prop
  | goal_200 : pattern_105_target goal_200_stmt

def pattern_105_stmt : Prop :=
  ∀ {target : Prop}, pattern_105_target target → target
theorem prove_pattern_105 : pattern_105_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

