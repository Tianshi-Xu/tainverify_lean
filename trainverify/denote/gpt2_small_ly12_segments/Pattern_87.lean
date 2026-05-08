/- Auto-generated pattern proof file.
   Pattern: 87
   Hash: bc865037473c9b3f
   Goals: 305
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_87_goalIds : List Nat := [305]
inductive pattern_87_target : Prop → Prop
  | goal_305 : pattern_87_target goal_305_stmt

def pattern_87_stmt : Prop :=
  ∀ {target : Prop}, pattern_87_target target → target
theorem prove_pattern_87 : pattern_87_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

