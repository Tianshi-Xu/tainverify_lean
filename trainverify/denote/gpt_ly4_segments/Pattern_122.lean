/- Auto-generated pattern proof file.
   Pattern: 122
   Hash: 0da2be15a57c889d
   Goals: 235
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_122_goalIds : List Nat := [235]
inductive pattern_122_target : Prop → Prop
  | goal_235 : pattern_122_target goal_235_stmt

def pattern_122_stmt : Prop :=
  ∀ {target : Prop}, pattern_122_target target → target
theorem prove_pattern_122 : pattern_122_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

