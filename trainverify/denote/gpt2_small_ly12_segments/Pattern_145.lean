/- Auto-generated pattern proof file.
   Pattern: 145
   Hash: 22d7a4b25021c9d1
   Goals: 401, 681
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_145_goalIds : List Nat := [401, 681]
inductive pattern_145_target : Prop → Prop
  | goal_401 : pattern_145_target goal_401_stmt
  | goal_681 : pattern_145_target goal_681_stmt

def pattern_145_stmt : Prop :=
  ∀ {target : Prop}, pattern_145_target target → target
theorem prove_pattern_145 : pattern_145_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

