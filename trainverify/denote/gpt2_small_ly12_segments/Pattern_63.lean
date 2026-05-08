/- Auto-generated pattern proof file.
   Pattern: 63
   Hash: 3f973f16bdf7edc0
   Goals: 144
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_63_goalIds : List Nat := [144]
inductive pattern_63_target : Prop → Prop
  | goal_144 : pattern_63_target goal_144_stmt

def pattern_63_stmt : Prop :=
  ∀ {target : Prop}, pattern_63_target target → target
theorem prove_pattern_63 : pattern_63_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

