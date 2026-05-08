/- Auto-generated pattern proof file.
   Pattern: 144
   Hash: ff126a488ffa9918
   Goals: 400
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_144_goalIds : List Nat := [400]
inductive pattern_144_target : Prop → Prop
  | goal_400 : pattern_144_target goal_400_stmt

def pattern_144_stmt : Prop :=
  ∀ {target : Prop}, pattern_144_target target → target
theorem prove_pattern_144 : pattern_144_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

