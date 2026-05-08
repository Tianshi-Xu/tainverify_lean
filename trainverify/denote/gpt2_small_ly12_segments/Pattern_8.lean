/- Auto-generated pattern proof file.
   Pattern: 8
   Hash: 760e172b5029dda0
   Goals: 9, 11, 13, 34, 36, 38, 59, 61, 63, 84, 86, 88, 109, 111, 113, 134, 136, 138, 159, 161, 163, 184, 186, 188, 209, 211, 213, 234, 236, 238, 259, 261, 263, 284, 286, 288
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_8_goalIds : List Nat := [9, 11, 13, 34, 36, 38, 59, 61, 63, 84, 86, 88, 109, 111, 113, 134, 136, 138, 159, 161, 163, 184, 186, 188, 209, 211, 213, 234, 236, 238, 259, 261, 263, 284, 286, 288]
inductive pattern_8_target : Prop → Prop
  | goal_9 : pattern_8_target goal_9_stmt
  | goal_11 : pattern_8_target goal_11_stmt
  | goal_13 : pattern_8_target goal_13_stmt
  | goal_34 : pattern_8_target goal_34_stmt
  | goal_36 : pattern_8_target goal_36_stmt
  | goal_38 : pattern_8_target goal_38_stmt
  | goal_59 : pattern_8_target goal_59_stmt
  | goal_61 : pattern_8_target goal_61_stmt
  | goal_63 : pattern_8_target goal_63_stmt
  | goal_84 : pattern_8_target goal_84_stmt
  | goal_86 : pattern_8_target goal_86_stmt
  | goal_88 : pattern_8_target goal_88_stmt
  | goal_109 : pattern_8_target goal_109_stmt
  | goal_111 : pattern_8_target goal_111_stmt
  | goal_113 : pattern_8_target goal_113_stmt
  | goal_134 : pattern_8_target goal_134_stmt
  | goal_136 : pattern_8_target goal_136_stmt
  | goal_138 : pattern_8_target goal_138_stmt
  | goal_159 : pattern_8_target goal_159_stmt
  | goal_161 : pattern_8_target goal_161_stmt
  | goal_163 : pattern_8_target goal_163_stmt
  | goal_184 : pattern_8_target goal_184_stmt
  | goal_186 : pattern_8_target goal_186_stmt
  | goal_188 : pattern_8_target goal_188_stmt
  | goal_209 : pattern_8_target goal_209_stmt
  | goal_211 : pattern_8_target goal_211_stmt
  | goal_213 : pattern_8_target goal_213_stmt
  | goal_234 : pattern_8_target goal_234_stmt
  | goal_236 : pattern_8_target goal_236_stmt
  | goal_238 : pattern_8_target goal_238_stmt
  | goal_259 : pattern_8_target goal_259_stmt
  | goal_261 : pattern_8_target goal_261_stmt
  | goal_263 : pattern_8_target goal_263_stmt
  | goal_284 : pattern_8_target goal_284_stmt
  | goal_286 : pattern_8_target goal_286_stmt
  | goal_288 : pattern_8_target goal_288_stmt

def pattern_8_stmt : Prop :=
  ∀ {target : Prop}, pattern_8_target target → target
theorem prove_pattern_8 : pattern_8_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

