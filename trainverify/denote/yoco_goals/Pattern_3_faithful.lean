/-
  Pattern_3_faithful.lean — 2026-07-06 upstream-reshape-fidelity variant of Pattern_3.

  This is the FROM-SCRATCH proof of `prove_pattern_3` built on top of Goal_3_faithful,
  which carries FW_reshape target shape params (unlike legacy Goal_3.lean whose
  reshape params were empty, making them identity-modelled in Denote).

  The old Pattern_3.lean (12k+ lines) is preserved untouched: it uses the OLD
  identity FW_reshape semantics and its already-proven L0/L1 lemmas remain
  formally valid but the `prove_goal_3` sorry there is UNPROVABLE because under
  identity reshape, `goal_3_stmt_cut_ringAttn` is mathematically false at
  layers ≥ 2 (see ANALYSIS_V2.md for the full root-cause chain).

  Under the new faithful reshape:
  - reshape [4096, 16, 64] → [4096, 1024] genuinely flattens head+dim,
    letting the downstream fw_linear go through the 2D branch,
    and the subsequent fw_view [4096, 1024] becomes a no-op.
  - SM: reshape-then-linear-then-view = reshape-flatten-then-linear-2D-then-noop.
  - PM: same on shards + allGather, and gather-then-reshape ≡ reshape-then-gather
    on shard-dim-0 (because reshape flattens preserving shard-0 semantics).
  - Hence sm_pm_router_L{k}_commute is TRUE for k = 0..23.

  Namespace: `TrainVerify.Denote.Pattern3Faithful`, disambiguated from
  `TrainVerify.Denote.Pattern3` in the legacy Pattern_3.lean.

  ═════════════════════════════════════════════════════════════════════════
  HISTORY (2026-07-06 evening):

  * First iteration (Worker "reduction infra", commit 74e0f20): produced a
    kernel-clean final-stack reduction chain that reduces prove_goal_3 to a
    single `sm_pm_router_commute_all` obligation. Split into 3 sub-obligations
    in commit c6e118d.

  * Second iteration (Worker B / L0 pilot, commit e9a7136): tried to prove
    `sm_pm_router_commute_L0` and DISCOVERED THE UPSTREAM GRAPH BUG —
    build_goal3_faithful.py's original backward-reachability slicer dropped
    PM's `rms_norm(14644,4704)->4705 + multiref(4705)->[11875..11879]` chain,
    leaving PM router paths reading unconstrained init leaves.

  * Third iteration (commit cc9aa2b): regenerated Goal_3_faithful.lean via
    clone-legacy strategy (preserves entire cut structure, patches only the
    420 FW_reshape struct literals). Fixed the upstream bug at its source.

  RESULT: the reduction infrastructure from commits 74e0f20 & c6e118d is now
  INVALIDATED because it hardcodes take-indices against the old broken
  1859-node pm graph (correct legacy pm has 1866 nodes). Needs regeneration
  by a fresh worker session against the corrected Goal_3_faithful.
  ═════════════════════════════════════════════════════════════════════════
-/
import denote.yoco_goals.Goal_3_faithful
import denote.yoco_goals.Pattern_1  -- reuse fw_topk_routing_snd_fst_allGather0_commute_2_of

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoalsFaithful

namespace TrainVerify.Denote.Pattern3Faithful

/-! ## TODO: next-session pickup

    Regenerate the final-stack reduction infrastructure (was in commits
    74e0f20 & c6e118d, invalidated by cc9aa2b upstream fix). The 24 router
    tids from `sm_goal_3_faithful` still are 4710, 4764, 4818, ..., 5900
    (unchanged). The take-indices into `pm_goal_3_faithful.nodes` need to
    be recomputed against the new 1866-node pm graph.

    Then prove the 24 layer commutes as originally planned — but this time
    they are TRUE (SM computes through, PM computes through, both meet at
    initGoal boundaries that link them correctly).
-/

/-- Top-level Pattern_3 proof under the faithful reshape semantics.
    Currently `sorry` — the reduction infrastructure and 24-layer induction
    both need to be redone against the corrected Goal_3_faithful (post-cc9aa2b). -/
theorem prove_goal_3 : goal_3_stmt_cut_ringAttn := by
  sorry

/-- Pattern 3 discharge (in the faithful variant). Mirrors the old
    pattern_3_target binding used in MainTheorem.lean. -/
def pattern_3_target : Prop := goal_3_stmt_cut_ringAttn

theorem prove_pattern_3 : pattern_3_target := prove_goal_3

end TrainVerify.Denote.Pattern3Faithful
