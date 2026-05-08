/- Auto-generated pattern proof file.
   Pattern: 141
   Hash: 6fe5909eca745485
   Goals: 396
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_141_goalIds : List Nat := [396]
inductive pattern_141_target : Prop → Prop
  | goal_396 : pattern_141_target goal_396_stmt

def pattern_141_stmt : Prop :=
  ∀ {target : Prop}, pattern_141_target target → target
theorem prove_pattern_141 : pattern_141_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

