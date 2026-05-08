/- Auto-generated pattern proof file.
   Pattern: 218
   Hash: 574af4a3647d8990
   Goals: 764, 768, 782, 820, 852, 866
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_218_goalIds : List Nat := [764, 768, 782, 820, 852, 866]
inductive pattern_218_target : Prop → Prop
  | goal_764 : pattern_218_target goal_764_stmt
  | goal_768 : pattern_218_target goal_768_stmt
  | goal_782 : pattern_218_target goal_782_stmt
  | goal_820 : pattern_218_target goal_820_stmt
  | goal_852 : pattern_218_target goal_852_stmt
  | goal_866 : pattern_218_target goal_866_stmt

def pattern_218_stmt : Prop :=
  ∀ {target : Prop}, pattern_218_target target → target
theorem prove_pattern_218 : pattern_218_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

