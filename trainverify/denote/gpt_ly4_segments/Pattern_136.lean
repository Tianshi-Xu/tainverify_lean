/- Auto-generated pattern proof file.
   Pattern: 136
   Hash: 03d3dfbf604868f7
   Goals: 283
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_136_goalIds : List Nat := [283]
inductive pattern_136_target : Prop → Prop
  | goal_283 : pattern_136_target goal_283_stmt

def pattern_136_stmt : Prop :=
  ∀ {target : Prop}, pattern_136_target target → target
theorem prove_pattern_136 : pattern_136_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

