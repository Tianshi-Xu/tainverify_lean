/- Auto-generated pattern proof file.
   Pattern: 120
   Hash: 0da2be15a57c889d
   Goals: 235
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_120_goalIds : List Nat := [235]
inductive pattern_120_target : Prop → Prop
  | goal_235 : pattern_120_target goal_235_stmt

def pattern_120_stmt : Prop :=
  ∀ {target : Prop}, pattern_120_target target → target
theorem prove_pattern_120 : pattern_120_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

