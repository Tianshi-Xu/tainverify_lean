/- Auto-generated pattern proof file.
   Pattern: 131
   Hash: d8751f17a8d75fdc
   Goals: 369, 474, 579
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_131_goalIds : List Nat := [369, 474, 579]
inductive pattern_131_target : Prop → Prop
  | goal_369 : pattern_131_target goal_369_stmt
  | goal_474 : pattern_131_target goal_474_stmt
  | goal_579 : pattern_131_target goal_579_stmt

def pattern_131_stmt : Prop :=
  ∀ {target : Prop}, pattern_131_target target → target
theorem prove_pattern_131 : pattern_131_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

