/- Auto-generated pattern proof file.
   Pattern: 71
   Hash: 86df561567ca4b6b
   Goals: 130
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_71_goalIds : List Nat := [130]
inductive pattern_71_target : Prop → Prop
  | goal_130 : pattern_71_target goal_130_stmt

def pattern_71_stmt : Prop :=
  ∀ {target : Prop}, pattern_71_target target → target
theorem prove_pattern_71 : pattern_71_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

