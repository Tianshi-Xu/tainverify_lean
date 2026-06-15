/- Auto-generated pattern proof file.
   Pattern: 76
   Hash: f376f24d00c25d0f
   Goals: 136, 260
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_76_goalIds : List Nat := [136, 260]
inductive pattern_76_target : Prop → Prop
  | goal_136 : pattern_76_target goal_136_stmt
  | goal_260 : pattern_76_target goal_260_stmt

def pattern_76_stmt : Prop :=
  ∀ {target : Prop}, pattern_76_target target → target
theorem prove_pattern_76 : pattern_76_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

