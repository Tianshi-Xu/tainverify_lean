/- Auto-generated pattern proof file.
   Pattern: 117
   Hash: ac7a477439832810
   Goals: 343, 483
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_117_goalIds : List Nat := [343, 483]
inductive pattern_117_target : Prop → Prop
  | goal_343 : pattern_117_target goal_343_stmt
  | goal_483 : pattern_117_target goal_483_stmt

def pattern_117_stmt : Prop :=
  ∀ {target : Prop}, pattern_117_target target → target
theorem prove_pattern_117 : pattern_117_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

