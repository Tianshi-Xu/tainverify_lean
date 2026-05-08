/- Auto-generated pattern proof file.
   Pattern: 149
   Hash: f3f43d2b370f1260
   Goals: 413, 448, 550, 585, 588, 620, 693, 725
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_149_goalIds : List Nat := [413, 448, 550, 585, 588, 620, 693, 725]
inductive pattern_149_target : Prop → Prop
  | goal_413 : pattern_149_target goal_413_stmt
  | goal_448 : pattern_149_target goal_448_stmt
  | goal_550 : pattern_149_target goal_550_stmt
  | goal_585 : pattern_149_target goal_585_stmt
  | goal_588 : pattern_149_target goal_588_stmt
  | goal_620 : pattern_149_target goal_620_stmt
  | goal_693 : pattern_149_target goal_693_stmt
  | goal_725 : pattern_149_target goal_725_stmt

def pattern_149_stmt : Prop :=
  ∀ {target : Prop}, pattern_149_target target → target
theorem prove_pattern_149 : pattern_149_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

