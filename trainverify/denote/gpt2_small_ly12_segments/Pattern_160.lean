/- Auto-generated pattern proof file.
   Pattern: 160
   Hash: efee555c383bc1be
   Goals: 451, 486, 547, 617, 652
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_160_goalIds : List Nat := [451, 486, 547, 617, 652]
inductive pattern_160_target : Prop → Prop
  | goal_451 : pattern_160_target goal_451_stmt
  | goal_486 : pattern_160_target goal_486_stmt
  | goal_547 : pattern_160_target goal_547_stmt
  | goal_617 : pattern_160_target goal_617_stmt
  | goal_652 : pattern_160_target goal_652_stmt

def pattern_160_stmt : Prop :=
  ∀ {target : Prop}, pattern_160_target target → target
theorem prove_pattern_160 : pattern_160_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

