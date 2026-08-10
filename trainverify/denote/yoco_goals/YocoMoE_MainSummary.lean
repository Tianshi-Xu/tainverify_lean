/- YocoMoE mixed-tier verification companion.

  This module records exactly the independently established tier for each
  pattern; it is not an all-cut or all-full theorem:

  * Pattern 1: legacy labels-qualified cut theorem, plus a joint witness for
    its cut shape/init/labels hypotheses.
  * Pattern 2: canonical full faithful theorem.  No full-contract joint
    witness is claimed here.
  * Pattern 3: legacy ring-attention cut theorem, plus a joint witness for its
    cut shape/init/cu_seqlens-pin hypotheses.
  * Pattern 4: legacy cut theorem, plus a joint witness for its cut shape/init
    hypotheses.
  * Pattern 5: ancestry-closed full theorem.  No separate witness is claimed
    here.

  In particular, the retired Pattern-2 cut witness is not imported: Pattern 2
  now exports `goal_2_stmt_full`, and the old cut-environment zero-store
  computation is not evidence for the full external-input contract.
-/
import denote.yoco_goals.Pattern_1
import denote.yoco_goals.Pattern_2
import denote.yoco_goals.Pattern_3
import denote.yoco_goals.Pattern_4
import denote.yoco_goals.Pattern_5
import denote.yoco_goals.Pattern_1_JointWitness
import denote.yoco_goals.Pattern_3_JointWitness
import denote.yoco_goals.Pattern_4_JointWitness

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns

namespace TrainVerify.Denote.YocoMoE.Main

/-- Honest mixed-tier companion for the five YOCO-MoE patterns.

    The theorem deliberately pairs witnesses only with the three legacy cut
    claims (Patterns 1, 3, and 4).  Patterns 2 and 5 are stated directly at
    their full theorem types; this module does not assert that their full
    hypothesis packages have a common zero-store witness. -/
theorem yoco_moe_mixed_tier_companion :
    -- Pattern 1: legacy labels-qualified cut.
    pattern_1_stmt ∧
    -- Pattern 2: canonical full faithful statement.
    goal_2_stmt_full ∧
    -- Pattern 3: legacy ring-attention cut.
    pattern_3_ring_legacy_stmt ∧
    -- Pattern 4: legacy cut.
    pattern_4_stmt ∧
    -- Pattern 5: ancestry-closed full statement.
    goal_5_stmt_full ∧
    -- Pattern 1 cut hypotheses are jointly satisfiable.
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_1_cutInitEnv ∧
      StoreShapesHold initPM pm_goal_1_cutInitEnv ∧
      InitGoalsHold pm_goal_1_cut.numRanks goal_1_cut_initGoals initSM initPM ∧
      (∀ l : Nat, l < 4096 → scalarToNat (valAt (initPM 4678) l) < 154880)) ∧
    -- Pattern 3 legacy ring-cut hypotheses are jointly satisfiable.
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_3InitEnv ∧
      StoreShapesHold initPM pm_goal_3InitEnv ∧
      InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM ∧
      initPM 5346 = cu_pin_value ∧
      initPM 5395 = cu_pin_value ∧
      initPM 5444 = cu_pin_value ∧
      initPM 5493 = cu_pin_value ∧
      initPM 5542 = cu_pin_value ∧
      initPM 5591 = cu_pin_value ∧
      initPM 5640 = cu_pin_value ∧
      initPM 5689 = cu_pin_value ∧
      initPM 5738 = cu_pin_value ∧
      initPM 5787 = cu_pin_value ∧
      initPM 5836 = cu_pin_value ∧
      initPM 5885 = cu_pin_value) ∧
    -- Pattern 4 cut hypotheses are jointly satisfiable.
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_4_cutInitEnv ∧
      StoreShapesHold initPM pm_goal_4_cutInitEnv ∧
      InitGoalsHold pm_goal_4_cut.numRanks goal_4_cut_initGoals initSM initPM) := by
  refine ⟨prove_pattern_1_plain_legacy,
          prove_pattern_2 pattern_2_target.goal_2,
          prove_pattern_3_ring_legacy,
          prove_pattern_4,
          prove_pattern_5 pattern_5_target.goal_5,
          pattern_1_joint_hypothesis_witness,
          pattern_3_ring_legacy_joint_hypothesis_witness,
          pattern_4_joint_hypothesis_witness⟩

end TrainVerify.Denote.YocoMoE.Main
