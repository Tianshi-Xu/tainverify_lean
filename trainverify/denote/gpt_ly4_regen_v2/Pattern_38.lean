/- Auto-generated pattern proof file.
   Pattern: 38
   Hash: 06efedb9860cad7c
   Goals: 67
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_38_goalIds : List Nat := [67]
inductive pattern_38_target : Prop → Prop
  | goal_67 : pattern_38_target goal_67_stmt

def pattern_38_stmt : Prop :=
  ∀ {target : Prop}, pattern_38_target target → target
theorem prove_pattern_38 : pattern_38_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

