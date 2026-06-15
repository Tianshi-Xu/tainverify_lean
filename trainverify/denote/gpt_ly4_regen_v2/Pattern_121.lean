/- Auto-generated pattern proof file.
   Pattern: 121
   Hash: e88410deedfe284a
   Goals: 236
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_121_goalIds : List Nat := [236]
inductive pattern_121_target : Prop → Prop
  | goal_236 : pattern_121_target goal_236_stmt

def pattern_121_stmt : Prop :=
  ∀ {target : Prop}, pattern_121_target target → target
theorem prove_pattern_121 : pattern_121_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

