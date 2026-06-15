/- Auto-generated pattern proof file.
   Pattern: 104
   Hash: ca845ebaeae424c9
   Goals: 198
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_104_goalIds : List Nat := [198]
inductive pattern_104_target : Prop → Prop
  | goal_198 : pattern_104_target goal_198_stmt

def pattern_104_stmt : Prop :=
  ∀ {target : Prop}, pattern_104_target target → target
theorem prove_pattern_104 : pattern_104_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

