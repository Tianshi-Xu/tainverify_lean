/- Auto-generated pattern proof file.
   Pattern: 1
   Hash: f21b0c4efc7a9a58
   Goals: 1
-/
import denote.GeneratedYOCO3B

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_1_goalIds : List Nat := [1]
inductive pattern_1_target : Prop → Prop
  | goal_1 : pattern_1_target goal_1_stmt

def pattern_1_stmt : Prop :=
  ∀ {target : Prop}, pattern_1_target target → target
theorem prove_pattern_1 : pattern_1_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

