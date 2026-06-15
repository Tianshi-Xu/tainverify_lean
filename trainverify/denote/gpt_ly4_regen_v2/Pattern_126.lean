/- Auto-generated pattern proof file.
   Pattern: 126
   Hash: f9e77ec7d2a424da
   Goals: 259, 269, 273, 285, 287, 295, 297, 299, 301, 309, 311
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_126_goalIds : List Nat := [259, 269, 273, 285, 287, 295, 297, 299, 301, 309, 311]
inductive pattern_126_target : Prop → Prop
  | goal_259 : pattern_126_target goal_259_stmt
  | goal_269 : pattern_126_target goal_269_stmt
  | goal_273 : pattern_126_target goal_273_stmt
  | goal_285 : pattern_126_target goal_285_stmt
  | goal_287 : pattern_126_target goal_287_stmt
  | goal_295 : pattern_126_target goal_295_stmt
  | goal_297 : pattern_126_target goal_297_stmt
  | goal_299 : pattern_126_target goal_299_stmt
  | goal_301 : pattern_126_target goal_301_stmt
  | goal_309 : pattern_126_target goal_309_stmt
  | goal_311 : pattern_126_target goal_311_stmt

def pattern_126_stmt : Prop :=
  ∀ {target : Prop}, pattern_126_target target → target
theorem prove_pattern_126 : pattern_126_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

