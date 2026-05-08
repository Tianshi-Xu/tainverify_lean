/- Auto-generated pattern proof file.
   Pattern: 86
   Hash: 56ea76b0a16086ef
   Goals: 292
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_86_goalIds : List Nat := [292]
inductive pattern_86_target : Prop → Prop
  | goal_292 : pattern_86_target goal_292_stmt

def pattern_86_stmt : Prop :=
  ∀ {target : Prop}, pattern_86_target target → target
theorem prove_pattern_86 : pattern_86_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

