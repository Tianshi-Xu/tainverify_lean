/- Auto-generated pattern proof file.
   Pattern: 96
   Hash: d106b8c17b065a7d
   Goals: 177
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_96_goalIds : List Nat := [177]
inductive pattern_96_target : Prop → Prop
  | goal_177 : pattern_96_target goal_177_stmt

def pattern_96_stmt : Prop :=
  ∀ {target : Prop}, pattern_96_target target → target
theorem prove_pattern_96 : pattern_96_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

