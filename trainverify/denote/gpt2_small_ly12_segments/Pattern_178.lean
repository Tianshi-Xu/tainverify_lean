/- Auto-generated pattern proof file.
   Pattern: 178
   Hash: b8d6a122b2d8550b
   Goals: 536
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_178_goalIds : List Nat := [536]
inductive pattern_178_target : Prop → Prop
  | goal_536 : pattern_178_target goal_536_stmt

def pattern_178_stmt : Prop :=
  ∀ {target : Prop}, pattern_178_target target → target
theorem prove_pattern_178 : pattern_178_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

