/- Auto-generated pattern proof file.
   Pattern: 83
   Hash: 782f341d1dcbc271
   Goals: 150, 154, 220, 222, 276, 280, 304, 306
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_83_goalIds : List Nat := [150, 154, 220, 222, 276, 280, 304, 306]
inductive pattern_83_target : Prop → Prop
  | goal_150 : pattern_83_target goal_150_stmt
  | goal_154 : pattern_83_target goal_154_stmt
  | goal_220 : pattern_83_target goal_220_stmt
  | goal_222 : pattern_83_target goal_222_stmt
  | goal_276 : pattern_83_target goal_276_stmt
  | goal_280 : pattern_83_target goal_280_stmt
  | goal_304 : pattern_83_target goal_304_stmt
  | goal_306 : pattern_83_target goal_306_stmt

def pattern_83_stmt : Prop :=
  ∀ {target : Prop}, pattern_83_target target → target
theorem prove_pattern_83 : pattern_83_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

