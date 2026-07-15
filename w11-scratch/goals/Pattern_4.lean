/- Auto-generated pattern proof file.
   Pattern: 4
   Hash: db8423289d6d3aff
   Goals: 4
-/
import denote.GeneratedYOCOMoE

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_4_goalIds : List Nat := [4]
inductive pattern_4_target : Prop → Prop
  | goal_4 : pattern_4_target goal_4_stmt_cut

def pattern_4_stmt : Prop :=
  ∀ {target : Prop}, pattern_4_target target → target
theorem prove_pattern_4 : pattern_4_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

