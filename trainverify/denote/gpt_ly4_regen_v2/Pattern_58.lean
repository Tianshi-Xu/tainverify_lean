/- Auto-generated pattern proof file.
   Pattern: 58
   Hash: 54d8683296d854fe
   Goals: 113, 139, 148, 174, 183, 209, 218, 244, 253
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_58_goalIds : List Nat := [113, 139, 148, 174, 183, 209, 218, 244, 253]
inductive pattern_58_target : Prop → Prop
  | goal_113 : pattern_58_target goal_113_stmt
  | goal_139 : pattern_58_target goal_139_stmt
  | goal_148 : pattern_58_target goal_148_stmt
  | goal_174 : pattern_58_target goal_174_stmt
  | goal_183 : pattern_58_target goal_183_stmt
  | goal_209 : pattern_58_target goal_209_stmt
  | goal_218 : pattern_58_target goal_218_stmt
  | goal_244 : pattern_58_target goal_244_stmt
  | goal_253 : pattern_58_target goal_253_stmt

def pattern_58_stmt : Prop :=
  ∀ {target : Prop}, pattern_58_target target → target
theorem prove_pattern_58 : pattern_58_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

