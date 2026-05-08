/- Auto-generated pattern proof file.
   Pattern: 183
   Hash: 1e046d063c67dc88
   Goals: 567, 645
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_183_goalIds : List Nat := [567, 645]
inductive pattern_183_target : Prop → Prop
  | goal_567 : pattern_183_target goal_567_stmt
  | goal_645 : pattern_183_target goal_645_stmt

def pattern_183_stmt : Prop :=
  ∀ {target : Prop}, pattern_183_target target → target
theorem prove_pattern_183 : pattern_183_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

