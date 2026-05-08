/- Auto-generated pattern proof file.
   Pattern: 78
   Hash: 532876336fe9165c
   Goals: 216
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_78_goalIds : List Nat := [216]
inductive pattern_78_target : Prop → Prop
  | goal_216 : pattern_78_target goal_216_stmt

def pattern_78_stmt : Prop :=
  ∀ {target : Prop}, pattern_78_target target → target
theorem prove_pattern_78 : pattern_78_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

