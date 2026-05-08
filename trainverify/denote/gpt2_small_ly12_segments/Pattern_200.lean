/- Auto-generated pattern proof file.
   Pattern: 200
   Hash: 54c081bfd052c863
   Goals: 711
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_200_goalIds : List Nat := [711]
inductive pattern_200_target : Prop → Prop
  | goal_711 : pattern_200_target goal_711_stmt

def pattern_200_stmt : Prop :=
  ∀ {target : Prop}, pattern_200_target target → target
theorem prove_pattern_200 : pattern_200_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

