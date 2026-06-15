/- Auto-generated pattern proof file.
   Pattern: 114
   Hash: 2bd4aed444fec486
   Goals: 219
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_114_goalIds : List Nat := [219]
inductive pattern_114_target : Prop → Prop
  | goal_219 : pattern_114_target goal_219_stmt

def pattern_114_stmt : Prop :=
  ∀ {target : Prop}, pattern_114_target target → target
theorem prove_pattern_114 : pattern_114_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

