/- Auto-generated pattern proof file.
   Pattern: 73
   Hash: 67f6188cec178bd5
   Goals: 133, 168, 203, 238
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_73_goalIds : List Nat := [133, 168, 203, 238]
inductive pattern_73_target : Prop → Prop
  | goal_133 : pattern_73_target goal_133_stmt
  | goal_168 : pattern_73_target goal_168_stmt
  | goal_203 : pattern_73_target goal_203_stmt
  | goal_238 : pattern_73_target goal_238_stmt

def pattern_73_stmt : Prop :=
  ∀ {target : Prop}, pattern_73_target target → target
theorem prove_pattern_73 : pattern_73_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

