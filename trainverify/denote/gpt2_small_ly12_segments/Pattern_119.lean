/- Auto-generated pattern proof file.
   Pattern: 119
   Hash: bc085c86710cda2b
   Goals: 349, 489
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_119_goalIds : List Nat := [349, 489]
inductive pattern_119_target : Prop → Prop
  | goal_349 : pattern_119_target goal_349_stmt
  | goal_489 : pattern_119_target goal_489_stmt

def pattern_119_stmt : Prop :=
  ∀ {target : Prop}, pattern_119_target target → target
theorem prove_pattern_119 : pattern_119_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

