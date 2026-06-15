/- Auto-generated pattern proof file.
   Pattern: 137
   Hash: bf5f66fa5be72f0a
   Goals: 289
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_137_goalIds : List Nat := [289]
inductive pattern_137_target : Prop → Prop
  | goal_289 : pattern_137_target goal_289_stmt

def pattern_137_stmt : Prop :=
  ∀ {target : Prop}, pattern_137_target target → target
theorem prove_pattern_137 : pattern_137_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

