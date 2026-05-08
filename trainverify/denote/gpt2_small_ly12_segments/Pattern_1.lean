/- Auto-generated pattern proof file.
   Pattern: 1
   Hash: 5ce1449adbcdff14
   Goals: 1
-/
import denote.gpt2_small_ly12_segments.GeneratedData

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

