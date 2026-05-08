/- Auto-generated pattern proof file.
   Pattern: 134
   Hash: 168454ce227c6777
   Goals: 378, 410, 445, 480, 515, 623, 690, 734
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_134_goalIds : List Nat := [378, 410, 445, 480, 515, 623, 690, 734]
inductive pattern_134_target : Prop → Prop
  | goal_378 : pattern_134_target goal_378_stmt
  | goal_410 : pattern_134_target goal_410_stmt
  | goal_445 : pattern_134_target goal_445_stmt
  | goal_480 : pattern_134_target goal_480_stmt
  | goal_515 : pattern_134_target goal_515_stmt
  | goal_623 : pattern_134_target goal_623_stmt
  | goal_690 : pattern_134_target goal_690_stmt
  | goal_734 : pattern_134_target goal_734_stmt

def pattern_134_stmt : Prop :=
  ∀ {target : Prop}, pattern_134_target target → target
theorem prove_pattern_134 : pattern_134_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

