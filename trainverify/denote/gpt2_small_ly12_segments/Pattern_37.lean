/- Auto-generated pattern proof file.
   Pattern: 37
   Hash: 362fe28a330ba7b8
   Goals: 54, 74, 99, 154, 224, 249
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_37_goalIds : List Nat := [54, 74, 99, 154, 224, 249]
inductive pattern_37_target : Prop → Prop
  | goal_54 : pattern_37_target goal_54_stmt
  | goal_74 : pattern_37_target goal_74_stmt
  | goal_99 : pattern_37_target goal_99_stmt
  | goal_154 : pattern_37_target goal_154_stmt
  | goal_224 : pattern_37_target goal_224_stmt
  | goal_249 : pattern_37_target goal_249_stmt

def pattern_37_stmt : Prop :=
  ∀ {target : Prop}, pattern_37_target target → target
theorem prove_pattern_37 : pattern_37_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

