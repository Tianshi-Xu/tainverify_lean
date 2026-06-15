/- Auto-generated pattern proof file.
   Pattern: 86
   Hash: a35896c0c0e79e76
   Goals: 159
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_86_goalIds : List Nat := [159]
inductive pattern_86_target : Prop → Prop
  | goal_159 : pattern_86_target goal_159_stmt

def pattern_86_stmt : Prop :=
  ∀ {target : Prop}, pattern_86_target target → target
theorem prove_pattern_86 : pattern_86_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

