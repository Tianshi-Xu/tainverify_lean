/- Auto-generated pattern proof file.
   Pattern: 140
   Hash: b87872210a5737be
   Goals: 394
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_140_goalIds : List Nat := [394]
inductive pattern_140_target : Prop → Prop
  | goal_394 : pattern_140_target goal_394_stmt

def pattern_140_stmt : Prop :=
  ∀ {target : Prop}, pattern_140_target target → target
theorem prove_pattern_140 : pattern_140_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

