/- Auto-generated pattern proof file.
   Pattern: 60
   Hash: 5f029b3bb3623d26
   Goals: 135
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_60_goalIds : List Nat := [135]
inductive pattern_60_target : Prop → Prop
  | goal_135 : pattern_60_target goal_135_stmt

def pattern_60_stmt : Prop :=
  ∀ {target : Prop}, pattern_60_target target → target
theorem prove_pattern_60 : pattern_60_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

