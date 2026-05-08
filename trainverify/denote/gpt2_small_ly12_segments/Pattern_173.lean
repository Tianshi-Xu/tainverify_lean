/- Auto-generated pattern proof file.
   Pattern: 173
   Hash: 4677e9d381800fc5
   Goals: 505
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_173_goalIds : List Nat := [505]
inductive pattern_173_target : Prop → Prop
  | goal_505 : pattern_173_target goal_505_stmt

def pattern_173_stmt : Prop :=
  ∀ {target : Prop}, pattern_173_target target → target
theorem prove_pattern_173 : pattern_173_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

