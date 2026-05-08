/- Auto-generated pattern proof file.
   Pattern: 146
   Hash: 392d014c0fc2b2c0
   Goals: 402, 612, 682
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_146_goalIds : List Nat := [402, 612, 682]
inductive pattern_146_target : Prop → Prop
  | goal_402 : pattern_146_target goal_402_stmt
  | goal_612 : pattern_146_target goal_612_stmt
  | goal_682 : pattern_146_target goal_682_stmt

def pattern_146_stmt : Prop :=
  ∀ {target : Prop}, pattern_146_target target → target
theorem prove_pattern_146 : pattern_146_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

