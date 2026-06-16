/- Auto-generated pattern proof file.
   Pattern: 137
   Hash: c362b37e8ea68259
   Goals: 284
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_137_goalIds : List Nat := [284]
inductive pattern_137_target : Prop → Prop
  | goal_284 : pattern_137_target goal_284_stmt

def pattern_137_stmt : Prop :=
  ∀ {target : Prop}, pattern_137_target target → target
theorem prove_pattern_137 : pattern_137_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

