/- Auto-generated pattern proof file.
   Pattern: 27
   Hash: 8bc48b286bacd2f6
   Goals: 35, 64, 89, 112, 114, 137, 139, 185, 212, 214, 237, 287
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_27_goalIds : List Nat := [35, 64, 89, 112, 114, 137, 139, 185, 212, 214, 237, 287]
inductive pattern_27_target : Prop → Prop
  | goal_35 : pattern_27_target goal_35_stmt
  | goal_64 : pattern_27_target goal_64_stmt
  | goal_89 : pattern_27_target goal_89_stmt
  | goal_112 : pattern_27_target goal_112_stmt
  | goal_114 : pattern_27_target goal_114_stmt
  | goal_137 : pattern_27_target goal_137_stmt
  | goal_139 : pattern_27_target goal_139_stmt
  | goal_185 : pattern_27_target goal_185_stmt
  | goal_212 : pattern_27_target goal_212_stmt
  | goal_214 : pattern_27_target goal_214_stmt
  | goal_237 : pattern_27_target goal_237_stmt
  | goal_287 : pattern_27_target goal_287_stmt

def pattern_27_stmt : Prop :=
  ∀ {target : Prop}, pattern_27_target target → target
theorem prove_pattern_27 : pattern_27_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

