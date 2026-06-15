/- Auto-generated pattern proof file.
   Pattern: 125
   Hash: e225aa80702b3daa
   Goals: 257, 267, 271, 281
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_125_goalIds : List Nat := [257, 267, 271, 281]
inductive pattern_125_target : Prop → Prop
  | goal_257 : pattern_125_target goal_257_stmt
  | goal_267 : pattern_125_target goal_267_stmt
  | goal_271 : pattern_125_target goal_271_stmt
  | goal_281 : pattern_125_target goal_281_stmt

def pattern_125_stmt : Prop :=
  ∀ {target : Prop}, pattern_125_target target → target
theorem prove_pattern_125 : pattern_125_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

