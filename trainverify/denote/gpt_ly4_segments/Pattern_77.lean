/- Auto-generated pattern proof file.
   Pattern: 77
   Hash: f376f24d00c25d0f
   Goals: 136, 260
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_77_goalIds : List Nat := [136, 260]
inductive pattern_77_target : Prop → Prop
  | goal_136 : pattern_77_target goal_136_stmt
  | goal_260 : pattern_77_target goal_260_stmt

def pattern_77_stmt : Prop :=
  ∀ {target : Prop}, pattern_77_target target → target
theorem prove_pattern_77 : pattern_77_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

