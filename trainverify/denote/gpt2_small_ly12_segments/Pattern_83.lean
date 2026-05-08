/- Auto-generated pattern proof file.
   Pattern: 83
   Hash: 8e72f0c639ca6add
   Goals: 269
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_83_goalIds : List Nat := [269]
inductive pattern_83_target : Prop → Prop
  | goal_269 : pattern_83_target goal_269_stmt

def pattern_83_stmt : Prop :=
  ∀ {target : Prop}, pattern_83_target target → target
theorem prove_pattern_83 : pattern_83_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

