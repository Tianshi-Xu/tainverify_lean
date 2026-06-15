/- Auto-generated pattern proof file.
   Pattern: 27
   Hash: 34ed5eb033b6d830
   Goals: 40
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_27_goalIds : List Nat := [40]
inductive pattern_27_target : Prop → Prop
  | goal_40 : pattern_27_target goal_40_stmt

def pattern_27_stmt : Prop :=
  ∀ {target : Prop}, pattern_27_target target → target
theorem prove_pattern_27 : pattern_27_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

