/- Auto-generated pattern proof file.
   Pattern: 97
   Hash: e0aaa81732960f7d
   Goals: 316, 318, 320, 351, 353, 355, 386, 388, 390, 421, 423, 425, 456, 458, 460, 491, 493, 495, 526, 528, 530, 561, 563, 565, 596, 598, 600, 631, 633, 635, 666, 668, 670, 701, 703, 705
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_97_goalIds : List Nat := [316, 318, 320, 351, 353, 355, 386, 388, 390, 421, 423, 425, 456, 458, 460, 491, 493, 495, 526, 528, 530, 561, 563, 565, 596, 598, 600, 631, 633, 635, 666, 668, 670, 701, 703, 705]
inductive pattern_97_target : Prop → Prop
  | goal_316 : pattern_97_target goal_316_stmt
  | goal_318 : pattern_97_target goal_318_stmt
  | goal_320 : pattern_97_target goal_320_stmt
  | goal_351 : pattern_97_target goal_351_stmt
  | goal_353 : pattern_97_target goal_353_stmt
  | goal_355 : pattern_97_target goal_355_stmt
  | goal_386 : pattern_97_target goal_386_stmt
  | goal_388 : pattern_97_target goal_388_stmt
  | goal_390 : pattern_97_target goal_390_stmt
  | goal_421 : pattern_97_target goal_421_stmt
  | goal_423 : pattern_97_target goal_423_stmt
  | goal_425 : pattern_97_target goal_425_stmt
  | goal_456 : pattern_97_target goal_456_stmt
  | goal_458 : pattern_97_target goal_458_stmt
  | goal_460 : pattern_97_target goal_460_stmt
  | goal_491 : pattern_97_target goal_491_stmt
  | goal_493 : pattern_97_target goal_493_stmt
  | goal_495 : pattern_97_target goal_495_stmt
  | goal_526 : pattern_97_target goal_526_stmt
  | goal_528 : pattern_97_target goal_528_stmt
  | goal_530 : pattern_97_target goal_530_stmt
  | goal_561 : pattern_97_target goal_561_stmt
  | goal_563 : pattern_97_target goal_563_stmt
  | goal_565 : pattern_97_target goal_565_stmt
  | goal_596 : pattern_97_target goal_596_stmt
  | goal_598 : pattern_97_target goal_598_stmt
  | goal_600 : pattern_97_target goal_600_stmt
  | goal_631 : pattern_97_target goal_631_stmt
  | goal_633 : pattern_97_target goal_633_stmt
  | goal_635 : pattern_97_target goal_635_stmt
  | goal_666 : pattern_97_target goal_666_stmt
  | goal_668 : pattern_97_target goal_668_stmt
  | goal_670 : pattern_97_target goal_670_stmt
  | goal_701 : pattern_97_target goal_701_stmt
  | goal_703 : pattern_97_target goal_703_stmt
  | goal_705 : pattern_97_target goal_705_stmt

def pattern_97_stmt : Prop :=
  ∀ {target : Prop}, pattern_97_target target → target
theorem prove_pattern_97 : pattern_97_stmt := by
  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.
  sorry

end TrainVerify.Denote.GeneratedPatterns

