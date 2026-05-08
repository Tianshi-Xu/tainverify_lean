/- Auto-generated pattern proof file.
   Pattern: 136
   Hash: cedf711f29cb33ce
   Goals: 380, 406, 441, 520, 616, 651
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_136_goalIds : List Nat := [380, 406, 441, 520, 616, 651]
inductive pattern_136_target : Prop → Prop
  | goal_380 : pattern_136_target goal_380_stmt
  | goal_406 : pattern_136_target goal_406_stmt
  | goal_441 : pattern_136_target goal_441_stmt
  | goal_520 : pattern_136_target goal_520_stmt
  | goal_616 : pattern_136_target goal_616_stmt
  | goal_651 : pattern_136_target goal_651_stmt

def pattern_136_stmt : Prop :=
  ∀ {target : Prop}, pattern_136_target target → target
theorem prove_pattern_136 : pattern_136_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

