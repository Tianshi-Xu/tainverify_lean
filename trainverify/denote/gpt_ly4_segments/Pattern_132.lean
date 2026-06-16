/- Auto-generated pattern proof file.
   Pattern: 132
   Hash: 57c487c375656b24
   Goals: 266, 290, 292
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_132_goalIds : List Nat := [266, 290, 292]
inductive pattern_132_target : Prop → Prop
  | goal_266 : pattern_132_target goal_266_stmt
  | goal_290 : pattern_132_target goal_290_stmt
  | goal_292 : pattern_132_target goal_292_stmt

def pattern_132_stmt : Prop :=
  ∀ {target : Prop}, pattern_132_target target → target
theorem prove_pattern_132 : pattern_132_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

