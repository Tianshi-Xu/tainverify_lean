/- Auto-generated pattern proof file.
   Pattern: 72
   Hash: be04bcc49a6bec2b
   Goals: 191, 244
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_72_goalIds : List Nat := [191, 244]
inductive pattern_72_target : Prop → Prop
  | goal_191 : pattern_72_target goal_191_stmt
  | goal_244 : pattern_72_target goal_244_stmt

def pattern_72_stmt : Prop :=
  ∀ {target : Prop}, pattern_72_target target → target
theorem prove_pattern_72 : pattern_72_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

