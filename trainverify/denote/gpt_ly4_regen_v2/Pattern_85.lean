/- Auto-generated pattern proof file.
   Pattern: 85
   Hash: d060918dd08d68ee
   Goals: 157
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_85_goalIds : List Nat := [157]
inductive pattern_85_target : Prop → Prop
  | goal_157 : pattern_85_target goal_157_stmt

def pattern_85_stmt : Prop :=
  ∀ {target : Prop}, pattern_85_target target → target
theorem prove_pattern_85 : pattern_85_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

