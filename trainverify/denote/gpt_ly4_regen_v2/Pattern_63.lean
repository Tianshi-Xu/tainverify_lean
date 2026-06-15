/- Auto-generated pattern proof file.
   Pattern: 63
   Hash: 25b31a4fd13f0085
   Goals: 121, 125, 160, 166, 193, 228
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_63_goalIds : List Nat := [121, 125, 160, 166, 193, 228]
inductive pattern_63_target : Prop → Prop
  | goal_121 : pattern_63_target goal_121_stmt
  | goal_125 : pattern_63_target goal_125_stmt
  | goal_160 : pattern_63_target goal_160_stmt
  | goal_166 : pattern_63_target goal_166_stmt
  | goal_193 : pattern_63_target goal_193_stmt
  | goal_228 : pattern_63_target goal_228_stmt

def pattern_63_stmt : Prop :=
  ∀ {target : Prop}, pattern_63_target target → target
theorem prove_pattern_63 : pattern_63_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

