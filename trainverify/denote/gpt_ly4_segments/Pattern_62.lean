/- Auto-generated pattern proof file.
   Pattern: 62
   Hash: 8a17453f255d6c1c
   Goals: 116, 118, 120, 151, 153, 155, 186, 188, 190, 221, 223, 225
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_62_goalIds : List Nat := [116, 118, 120, 151, 153, 155, 186, 188, 190, 221, 223, 225]
inductive pattern_62_target : Prop → Prop
  | goal_116 : pattern_62_target goal_116_stmt
  | goal_118 : pattern_62_target goal_118_stmt
  | goal_120 : pattern_62_target goal_120_stmt
  | goal_151 : pattern_62_target goal_151_stmt
  | goal_153 : pattern_62_target goal_153_stmt
  | goal_155 : pattern_62_target goal_155_stmt
  | goal_186 : pattern_62_target goal_186_stmt
  | goal_188 : pattern_62_target goal_188_stmt
  | goal_190 : pattern_62_target goal_190_stmt
  | goal_221 : pattern_62_target goal_221_stmt
  | goal_223 : pattern_62_target goal_223_stmt
  | goal_225 : pattern_62_target goal_225_stmt

def pattern_62_stmt : Prop :=
  ∀ {target : Prop}, pattern_62_target target → target
theorem prove_pattern_62 : pattern_62_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

