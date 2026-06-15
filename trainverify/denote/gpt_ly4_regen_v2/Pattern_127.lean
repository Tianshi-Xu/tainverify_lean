/- Auto-generated pattern proof file.
   Pattern: 127
   Hash: 728f1d55e9e12045
   Goals: 261, 263, 277, 293, 307
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_127_goalIds : List Nat := [261, 263, 277, 293, 307]
inductive pattern_127_target : Prop → Prop
  | goal_261 : pattern_127_target goal_261_stmt
  | goal_263 : pattern_127_target goal_263_stmt
  | goal_277 : pattern_127_target goal_277_stmt
  | goal_293 : pattern_127_target goal_293_stmt
  | goal_307 : pattern_127_target goal_307_stmt

def pattern_127_stmt : Prop :=
  ∀ {target : Prop}, pattern_127_target target → target
theorem prove_pattern_127 : pattern_127_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

