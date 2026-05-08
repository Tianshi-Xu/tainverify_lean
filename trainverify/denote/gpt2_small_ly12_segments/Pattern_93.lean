/- Auto-generated pattern proof file.
   Pattern: 93
   Hash: aac94f9507845964
   Goals: 312, 338, 347, 373, 382, 408, 417, 443, 452, 478, 487, 513, 522, 548, 557, 583, 592, 618, 627, 653, 662, 688, 697, 723
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_93_goalIds : List Nat := [312, 338, 347, 373, 382, 408, 417, 443, 452, 478, 487, 513, 522, 548, 557, 583, 592, 618, 627, 653, 662, 688, 697, 723]
inductive pattern_93_target : Prop → Prop
  | goal_312 : pattern_93_target goal_312_stmt
  | goal_338 : pattern_93_target goal_338_stmt
  | goal_347 : pattern_93_target goal_347_stmt
  | goal_373 : pattern_93_target goal_373_stmt
  | goal_382 : pattern_93_target goal_382_stmt
  | goal_408 : pattern_93_target goal_408_stmt
  | goal_417 : pattern_93_target goal_417_stmt
  | goal_443 : pattern_93_target goal_443_stmt
  | goal_452 : pattern_93_target goal_452_stmt
  | goal_478 : pattern_93_target goal_478_stmt
  | goal_487 : pattern_93_target goal_487_stmt
  | goal_513 : pattern_93_target goal_513_stmt
  | goal_522 : pattern_93_target goal_522_stmt
  | goal_548 : pattern_93_target goal_548_stmt
  | goal_557 : pattern_93_target goal_557_stmt
  | goal_583 : pattern_93_target goal_583_stmt
  | goal_592 : pattern_93_target goal_592_stmt
  | goal_618 : pattern_93_target goal_618_stmt
  | goal_627 : pattern_93_target goal_627_stmt
  | goal_653 : pattern_93_target goal_653_stmt
  | goal_662 : pattern_93_target goal_662_stmt
  | goal_688 : pattern_93_target goal_688_stmt
  | goal_697 : pattern_93_target goal_697_stmt
  | goal_723 : pattern_93_target goal_723_stmt

def pattern_93_stmt : Prop :=
  ∀ {target : Prop}, pattern_93_target target → target
theorem prove_pattern_93 : pattern_93_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

