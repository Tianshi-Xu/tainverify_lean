/- Auto-generated pattern proof file.
   Pattern: 128
   Hash: 05d53b83208ff068
   Goals: 262, 264, 278, 294, 308
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_128_goalIds : List Nat := [262, 264, 278, 294, 308]
inductive pattern_128_target : Prop → Prop
  | goal_262 : pattern_128_target goal_262_stmt
  | goal_264 : pattern_128_target goal_264_stmt
  | goal_278 : pattern_128_target goal_278_stmt
  | goal_294 : pattern_128_target goal_294_stmt
  | goal_308 : pattern_128_target goal_308_stmt

def pattern_128_stmt : Prop :=
  ∀ {target : Prop}, pattern_128_target target → target
theorem prove_pattern_128 : pattern_128_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

