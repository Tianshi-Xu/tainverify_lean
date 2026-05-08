/- Auto-generated pattern proof file.
   Pattern: 187
   Hash: ccfd8819424851fd
   Goals: 574
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_187_goalIds : List Nat := [574]
inductive pattern_187_target : Prop → Prop
  | goal_574 : pattern_187_target goal_574_stmt

def pattern_187_stmt : Prop :=
  ∀ {target : Prop}, pattern_187_target target → target
theorem prove_pattern_187 : pattern_187_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

