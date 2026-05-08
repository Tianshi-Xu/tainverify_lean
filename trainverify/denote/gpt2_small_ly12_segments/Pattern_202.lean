/- Auto-generated pattern proof file.
   Pattern: 202
   Hash: 221b4aa207cc6e7b
   Goals: 713
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_202_goalIds : List Nat := [713]
inductive pattern_202_target : Prop → Prop
  | goal_713 : pattern_202_target goal_713_stmt

def pattern_202_stmt : Prop :=
  ∀ {target : Prop}, pattern_202_target target → target
theorem prove_pattern_202 : pattern_202_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

