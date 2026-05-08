/- Auto-generated pattern proof file.
   Pattern: 105
   Hash: 107bb104f8b17b3d
   Goals: 328, 678
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_105_goalIds : List Nat := [328, 678]
inductive pattern_105_target : Prop → Prop
  | goal_328 : pattern_105_target goal_328_stmt
  | goal_678 : pattern_105_target goal_678_stmt

def pattern_105_stmt : Prop :=
  ∀ {target : Prop}, pattern_105_target target → target
theorem prove_pattern_105 : pattern_105_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

