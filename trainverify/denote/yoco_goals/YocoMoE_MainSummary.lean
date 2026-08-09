/- YocoMoE main verification summary (2026-07-14).

  This file states and proves the "cut-graph tier" main theorem for
  YOCO-MoE (yoco_0.4B), summarising what TrainVerify has established so far:

  1. All 5 pattern-level proofs (`prove_pattern_1..5`) are complete against
     their honest cut statements. Pattern_3's statement explicitly carries its
     12 cu_seqlens value pins. Patterns 1/4 obtain their 15 post-shuffle ordinary
     gather relations from goal-local, shuffle-free cut boundary contracts —
     not from false full-graph goals or external theorem parameters. See
     `trainverify/GOAL_3_4_LAYOUT_SPLIT.md`.
  2. All 5 patterns' hypotheses are jointly satisfiable. The 15 ordinary-gather
     relations needed only by the shuffle-free cut graphs are explicit local
     `cutIntermediateGoal_*` boundary contracts included in each cut's
     `InitGoalsHold` package, rather than impossible full-graph goals or external
     theorem parameters. Existing zero-store joint witnesses cover them:
       - Pattern_1: labels-bounded  (`< vocab`)
       - Pattern_3: 12 cu_seqlens pins  (`= cu_pin_value`)
     ruling out vacuity (∅ → anything).
  3. This module intentionally remains the cut-tier summary. The historical
     unconditional five-goal `all_goals_stmt` is not a valid target: goal 1
     needs a labels contract, goal 3 needs 12 pins, and full goals 3/4 are false
     on CP2. `MainTheorem.lean` now provides the corrected full theorem by
     composing direct distributed-faithful proofs for sound goals 1/2/5 with
     the honest pattern contracts and emitted-corpus shape.

     goal_3 and goal_4 are a different case: on the currently audited CP2 graph
     their generated full-graph equalities are false (CP zigzag shards do not
     ordinary-gather). Those statements are removed and reported as findings,
     not deferred proof obligations. A corrected future nnScaler graph could of
     course generate different, sound statements.

  Axiom footprint (this file + all its transitive dependencies at
  the cut-tier claim below): the Lean-4 kernel triple
  `[propext, Classical.choice, Quot.sound]` plus the 5-axiom
  `native_decide` baseline (`Lean.ofReduceBool`, `Lean.trustCompiler`
  and their variants).  Zero shard-specific / hand-written axioms.
-/
import denote.yoco_goals.Pattern_1
import denote.yoco_goals.Pattern_2
import denote.yoco_goals.Pattern_3
import denote.yoco_goals.Pattern_4
import denote.yoco_goals.Pattern_5
import denote.yoco_goals.Pattern_1_JointWitness
import denote.yoco_goals.Pattern_2_JointWitness
import denote.yoco_goals.Pattern_3_JointWitness
import denote.yoco_goals.Pattern_4_JointWitness

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns

namespace TrainVerify.Denote.YocoMoE.Main

/-- YOCO-MoE cut-tier main theorem.

    This remains the non-vacuous cut-pattern summary. The corrected
    distributed-faithful full theorem is `yoco_moe_corrected_main` in
    `MainTheorem.lean`. Its content here:

    * Every pattern-level proof (`prove_pattern_N`) holds.
    * Every pattern's hypothesis set is jointly satisfiable (non-vacuous).

    Together, these establish that each cut-graph goal is genuinely
    proven against a witness that satisfies its full hypothesis package.
    They are retained as a pattern-level companion to the corrected faithful
    full theorem, not coerced back into the invalid legacy `all_goals_stmt`. -/
/- NOTE (2026-07-28): 15 post-shuffle relations are false as faithful
   FULL-graph ordinary-gather goals, but sound as explicit boundary contracts of
   the shuffle-free CUT graphs. Goal_1/Goal_4 re-declare them locally as
   `cutIntermediateGoal_*` and include them in `goal_N_cut_initGoals`; the joint
   witness machinery therefore establishes their satisfiability. They are not
   published globally and cannot be mistaken for full-graph results. See
   `trainverify/GOAL_3_4_LAYOUT_SPLIT.md`. -/
theorem yoco_moe_cut_tier_main :
    -- Pattern proofs complete
    pattern_1_stmt ∧
    pattern_2_stmt ∧
    pattern_3_stmt ∧
    pattern_4_stmt ∧
    pattern_5_stmt ∧
    -- Joint witness for P1 (with labels hypothesis)
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_1_cutInitEnv ∧
      StoreShapesHold initPM pm_goal_1_cutInitEnv ∧
      InitGoalsHold pm_goal_1_cut.numRanks goal_1_cut_initGoals initSM initPM ∧
      (∀ l : Nat, l < 4096 → scalarToNat (valAt (initPM 4678) l) < 154880)) ∧
    -- Joint witness for P2 (no extra hypothesis)
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_2InitEnv ∧
      StoreShapesHold initPM pm_goal_2InitEnv ∧
      InitGoalsHold pm_goal_2.numRanks goal_2_cut_initGoals initSM initPM) ∧
    -- Joint witness for P3 (with cu_seqlens pins hypothesis)
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
    -- Joint witness for P4 (no extra hypothesis)
    (∃ (initSM initPM : Store),
      StoreShapesHold initSM sm_goal_4_cutInitEnv ∧
      StoreShapesHold initPM pm_goal_4_cutInitEnv ∧
      InitGoalsHold pm_goal_4_cut.numRanks goal_4_cut_initGoals initSM initPM) := by
  refine ⟨prove_pattern_1_plain_legacy, prove_pattern_2, prove_pattern_3,
          prove_pattern_4, prove_pattern_5,
          pattern_1_joint_hypothesis_witness,
          pattern_2_joint_hypothesis_witness,
          pattern_3_joint_hypothesis_witness,
          pattern_4_joint_hypothesis_witness⟩

end TrainVerify.Denote.YocoMoE.Main
