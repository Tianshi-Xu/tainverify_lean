/- Auto-generated pattern proof file.
   Pattern: 139
   Hash: bd1ff169297e3ea4
   Goals: 392, 715
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_139_goalIds : List Nat := [392, 715]
inductive pattern_139_target : Prop → Prop
  | goal_392 : pattern_139_target goal_392_stmt
  | goal_715 : pattern_139_target goal_715_stmt

def pattern_139_stmt : Prop :=
  ∀ {target : Prop}, pattern_139_target target → target
theorem prove_pattern_139 : pattern_139_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

