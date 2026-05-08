/- Auto-generated pattern proof file.
   Pattern: 139
   Hash: bf5f66fa5be72f0a
   Goals: 289
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_139_goalIds : List Nat := [289]
inductive pattern_139_target : Prop → Prop
  | goal_289 : pattern_139_target goal_289_stmt

def pattern_139_stmt : Prop :=
  ∀ {target : Prop}, pattern_139_target target → target
theorem prove_pattern_139 : pattern_139_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

