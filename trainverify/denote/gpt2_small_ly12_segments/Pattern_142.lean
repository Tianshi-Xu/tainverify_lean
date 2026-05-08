/- Auto-generated pattern proof file.
   Pattern: 142
   Hash: dc9e058cbda65265
   Goals: 397
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_142_goalIds : List Nat := [397]
inductive pattern_142_target : Prop → Prop
  | goal_397 : pattern_142_target goal_397_stmt

def pattern_142_stmt : Prop :=
  ∀ {target : Prop}, pattern_142_target target → target
theorem prove_pattern_142 : pattern_142_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

