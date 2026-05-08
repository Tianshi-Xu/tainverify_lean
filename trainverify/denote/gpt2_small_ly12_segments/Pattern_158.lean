/- Auto-generated pattern proof file.
   Pattern: 158
   Hash: 5fa001e9a332644f
   Goals: 436, 611
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_158_goalIds : List Nat := [436, 611]
inductive pattern_158_target : Prop → Prop
  | goal_436 : pattern_158_target goal_436_stmt
  | goal_611 : pattern_158_target goal_611_stmt

def pattern_158_stmt : Prop :=
  ∀ {target : Prop}, pattern_158_target target → target
theorem prove_pattern_158 : pattern_158_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

