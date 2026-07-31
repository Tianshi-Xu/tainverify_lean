/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.Instances
import denote.yoco_goals.L23FaithfulLossGoals
import denote.yoco_goals.SDChainHead
import denote.yoco_goals.IntermediateReconstruction

/-!
# Corrected YOCO-MoE main theorem

The historical generated `all_goals_stmt` required five unconditional ordinary
full-graph equalities. That specification is not true on the audited CP2 graph:
router-stack goals 3/4 gather zigzag-owned shards before unshuffle. This module
therefore composes exactly the claims that are both meaningful and proved:

* full-graph distributed-faithful value equalities for top-level goals 1/2,
  plus the complete Goal 5 lineage result;
* the strongest verified statement for each historical goal: full ring-aware for
  goals 1/2, provenance-derived cut for goal 3, cut for goal 4, and full for 5;
* a kernel-checked emitted-corpus shape showing that the generated full-goal
  list now contains only goals 1, 2, and 5 and that the ordinary/zigzag lists
  retain their audited cardinalities.

The two omitted IDs, 4675/4676, are established as findings by the separate
source/runtime audit, not by this Lean bookkeeping and not by pretending that a
generic fixture is a theorem about the concrete graph. See
`GOAL_3_4_LAYOUT_SPLIT.md` and `UPSTREAM_NNSCALER_RVD_ZIGZAG.md`.
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 10000000
set_option maxHeartbeats 16000000

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote.GeneratedPatternInstances

namespace TrainVerify.Denote.YocoMoE.CorrectedMain
noncomputable section

/-- The three sound top-level distributed-faithful results. Goals 1/2 expose
their proved value equalities; Goal 5 exposes the complete lineage result. -/
def FaithfulTopLevelValueMain : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM smInitEnv →
    StoreShapesHold initPM pmInitEnv →
    InitGoalsHold pm.numRanks initGoals initSM initPM →
    InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM →
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) →
    (denoteGraphDistributedFaithful pm initPM 13257).shape.getD 0 0 = 2048 →
    (∀ l < 2048 * 2,
      scalarToNat (valAt (denoteGraphDistributedFaithful pm initPM 4678) l) < 154880) →
    denoteGraphDistributedFaithful sm initSM 4673 =
        denoteGraphDistributedFaithful pm initPM 4673 ∧
      denoteGraphDistributedFaithful sm initSM 4674 =
        denoteGraphDistributedFaithful pm initPM 4674 ∧
      InitGoalHolds pm.numRanks goal_5
        (denoteGraphDistributedFaithful sm initSM)
        (denoteGraphDistributedFaithful pm initPM)

/-- The five historical obligations at their strongest verified levels:
Goals 1/2 are full ring-aware theorems, Goal 3 is the cut theorem under the
generated value-class plus anchor contract, Goal 4 remains cut-only because its
ordinary full equality is false, and Goal 5 is full. -/
def HonestPatternTier : Prop :=
  goal_1_stmt_ringAttn_full_with_labels ∧
  goal_2_stmt_ringAttn_full ∧
  TrainVerify.Denote.YocoMoE.Goal3Pins.goal_3_stmt_with_value_class ∧
  goal_4_stmt_cut ∧
  goal_5_stmt

/-- Machine-checkable bookkeeping for the emitted sound corpus only. This does
not claim to prove the source/runtime counterexamples for omitted goals 3/4. -/
def EmittedCorpusShape : Prop :=
  goals = [goal_1, goal_2, goal_5] ∧
  all_intermediateGoals_list.length = 646 ∧
  zigzagGoals.length = 505

/-- Direct composition of the three sound faithful top-level proofs. -/
theorem faithful_top_level_value_main : FaithfulTopLevelValueMain := by
  unfold FaithfulTopLevelValueMain
  intro initSM initPM hSM hPM hInit hValues hCu hx0 hlabels
  refine ⟨?_, ?_, ?_⟩
  · exact recon_goal_4673_faithful initSM initPM hSM hPM hInit hValues hCu hx0 hlabels
  · exact recon_goal_4674_faithful initSM initPM hSM hPM hInit hValues hCu hx0
  · exact recon_goal_5_faithful initSM initPM hSM hPM hInit

/-- The old pattern tier is now completely sorry-free once each instance keeps
its real caller contract. -/
theorem honest_pattern_tier : HonestPatternTier := by
  exact ⟨prove_goal_1_full_ringAttn,
    prove_goal_2_full_from_pattern_2,
    prove_goal_3_from_pattern_3,
    prove_goal_4_from_pattern_4,
    prove_goal_5_from_pattern_5⟩

/-- The generated full-goal list excludes the two audited false equalities while
retaining all 646 ordinary and 505 zigzag intermediate obligations. -/
theorem emitted_corpus_shape : EmittedCorpusShape := by
  unfold EmittedCorpusShape
  native_decide

/-- Corrected conditional full-goal and honest-pattern YOCO summary.

The full faithful tier intentionally exposes `hValues`, `hCu`, `hx0`, and the
label bound as caller contracts; this theorem does not claim a joint witness for
those full-tier assumptions. Pattern-tier non-vacuity witnesses are provided by
`YocoMoE_MainSummary.lean`. -/
theorem yoco_moe_corrected_main :
    FaithfulTopLevelValueMain ∧ HonestPatternTier ∧ EmittedCorpusShape := by
  exact ⟨faithful_top_level_value_main, honest_pattern_tier, emitted_corpus_shape⟩

end
end TrainVerify.Denote.YocoMoE.CorrectedMain
