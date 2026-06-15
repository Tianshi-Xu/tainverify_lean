/- Auto-generated pattern proof file.
   Pattern: 60
   Hash: 311c9abadc02f73b
   Goals: 115, 117, 152, 189, 224
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_60_goalIds : List Nat := [115, 117, 152, 189, 224]
inductive pattern_60_target : Prop → Prop
  | goal_115 : pattern_60_target goal_115_stmt
  | goal_117 : pattern_60_target goal_117_stmt
  | goal_152 : pattern_60_target goal_152_stmt
  | goal_189 : pattern_60_target goal_189_stmt
  | goal_224 : pattern_60_target goal_224_stmt

def pattern_60_stmt : Prop :=
  ∀ {target : Prop}, pattern_60_target target → target
theorem prove_pattern_60 : pattern_60_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

