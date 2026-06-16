/- Auto-generated pattern proof file.
   Pattern: 97
   Hash: efee555c383bc1be
   Goals: 172
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_97_goalIds : List Nat := [172]
inductive pattern_97_target : Prop → Prop
  | goal_172 : pattern_97_target goal_172_stmt

def pattern_97_stmt : Prop :=
  ∀ {target : Prop}, pattern_97_target target → target
theorem prove_pattern_97 : pattern_97_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

