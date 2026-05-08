/- Auto-generated pattern proof file.
   Pattern: 186
   Hash: 7ebe6c30ad4ff5a7
   Goals: 573
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_186_goalIds : List Nat := [573]
inductive pattern_186_target : Prop → Prop
  | goal_573 : pattern_186_target goal_573_stmt

def pattern_186_stmt : Prop :=
  ∀ {target : Prop}, pattern_186_target target → target
theorem prove_pattern_186 : pattern_186_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

