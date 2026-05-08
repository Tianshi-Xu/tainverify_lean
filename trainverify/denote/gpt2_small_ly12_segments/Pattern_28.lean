/- Auto-generated pattern proof file.
   Pattern: 28
   Hash: 34ed5eb033b6d830
   Goals: 40
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_28_goalIds : List Nat := [40]
inductive pattern_28_target : Prop → Prop
  | goal_40 : pattern_28_target goal_40_stmt

def pattern_28_stmt : Prop :=
  ∀ {target : Prop}, pattern_28_target target → target
theorem prove_pattern_28 : pattern_28_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

