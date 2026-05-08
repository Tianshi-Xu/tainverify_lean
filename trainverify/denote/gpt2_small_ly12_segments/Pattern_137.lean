/- Auto-generated pattern proof file.
   Pattern: 137
   Hash: 87e3e47c8d323ee4
   Goals: 381, 407, 416, 442, 521
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_137_goalIds : List Nat := [381, 407, 416, 442, 521]
inductive pattern_137_target : Prop → Prop
  | goal_381 : pattern_137_target goal_381_stmt
  | goal_407 : pattern_137_target goal_407_stmt
  | goal_416 : pattern_137_target goal_416_stmt
  | goal_442 : pattern_137_target goal_442_stmt
  | goal_521 : pattern_137_target goal_521_stmt

def pattern_137_stmt : Prop :=
  ∀ {target : Prop}, pattern_137_target target → target
theorem prove_pattern_137 : pattern_137_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

