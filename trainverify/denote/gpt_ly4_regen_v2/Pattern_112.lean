/- Auto-generated pattern proof file.
   Pattern: 112
   Hash: 1b4403d68cc65102
   Goals: 211, 214, 246, 249
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_112_goalIds : List Nat := [211, 214, 246, 249]
inductive pattern_112_target : Prop → Prop
  | goal_211 : pattern_112_target goal_211_stmt
  | goal_214 : pattern_112_target goal_214_stmt
  | goal_246 : pattern_112_target goal_246_stmt
  | goal_249 : pattern_112_target goal_249_stmt

def pattern_112_stmt : Prop :=
  ∀ {target : Prop}, pattern_112_target target → target
theorem prove_pattern_112 : pattern_112_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

