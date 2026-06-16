/- Auto-generated pattern proof file.
   Pattern: 120
   Hash: 2a803104e732b46c
   Goals: 232
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_120_goalIds : List Nat := [232]
inductive pattern_120_target : Prop → Prop
  | goal_232 : pattern_120_target goal_232_stmt

def pattern_120_stmt : Prop :=
  ∀ {target : Prop}, pattern_120_target target → target
theorem prove_pattern_120 : pattern_120_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

