/- Auto-generated pattern proof file.
   Pattern: 136
   Hash: 0f879ddfa7918fbd
   Goals: 288, 298, 302, 312
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_136_goalIds : List Nat := [288, 298, 302, 312]
inductive pattern_136_target : Prop → Prop
  | goal_288 : pattern_136_target goal_288_stmt
  | goal_298 : pattern_136_target goal_298_stmt
  | goal_302 : pattern_136_target goal_302_stmt
  | goal_312 : pattern_136_target goal_312_stmt

def pattern_136_stmt : Prop :=
  ∀ {target : Prop}, pattern_136_target target → target
theorem prove_pattern_136 : pattern_136_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

