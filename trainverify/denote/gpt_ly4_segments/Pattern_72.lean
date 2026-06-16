/- Auto-generated pattern proof file.
   Pattern: 72
   Hash: 60b2b79ebfc5c86d
   Goals: 131
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_72_goalIds : List Nat := [131]
inductive pattern_72_target : Prop → Prop
  | goal_131 : pattern_72_target goal_131_stmt

def pattern_72_stmt : Prop :=
  ∀ {target : Prop}, pattern_72_target target → target
theorem prove_pattern_72 : pattern_72_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

