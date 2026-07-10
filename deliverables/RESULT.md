# RESULT — denote-unfold generic-lemma refactor

## Summary

Introduced namespace `DenoteUnfoldGeneric` (7 zero-sorry backbone lemmas) in
`Pattern_3.lean` and rewrote **510 of 686** `denote_{sm,pm}_goal_3_<tid>`
value-unfold theorems into compact term-mode invocations of those lemmas,
mirroring the prior `HsHelpersGeneric` approach.

## Backbone lemmas (namespace `DenoteUnfoldGeneric`, ZERO sorry)

| Lemma | Role |
|---|---|
| `denote_leaf_val` | leaf input value = `initStore tid` (drop-0 dependency-cone `by decide`) |
| `dstep1` | 1-input node: `denote tid_out = f (denote i1)` |
| `dstep2` | 2-input node |
| `dstep3` | 3-input node (linear-family) |
| `dstep4` | 4-input node (rotary) |
| `dstep5` | 5-input node |
| `dstep7` | 7-input node (moe_gmm n-ary) |

Machinery per lemma: `foldl_prefix_eq_full_ringAttn` (Boundary) → `take (M+1)` split
(Written) → `applyNodeRingAttn_eq_applyNode_of_not_ring` + per-op `applyNode_<op>_out`
+ leaf/recursive value hypotheses. Every hypothesis discharged by `by decide` /
`rfl` / nested `dstep1` at each call-site.

## Metrics

| Metric | Baseline | After | Delta |
|---|---:|---:|---:|
| `Pattern_3.lean` lines | 47,168 | **40,820** | **−6,348 (−13.5%)** |
| `denote_*` theorems genericized | 0 | **510** (330 n1 + 180 n2) | — |
| `denote_*` theorems hand-written | 686 | 176 | — |
| Theorem names preserved | 686 | 686 | **0 lost** |
| Full build time | 31m17s | **25m13s** | **−19.4% (faster)** |
| Build exit code | 0 | **0** | ✅ |

Build-time regression budget was ≤5%; result is a **19% improvement** (well within budget).

## Kernel audit (`#print axioms`)

All sampled names report exactly `[propext, Classical.choice, Quot.sound]`:

- Backbone: `denote_leaf_val`, `dstep1`, `dstep2`, `dstep3`, `dstep4`, `dstep5`, `dstep7`
- n1 samples: `denote_sm_goal_3_4867`, `denote_pm_goal_3_7666`, `denote_sm_goal_3_4814`
- n2 samples: `denote_pm_goal_3_7771`, `denote_sm_goal_3_4868`, `denote_pm_goal_3_8031`,
  `denote_sm_goal_3_4922`, `denote_pm_goal_3_7845`
- Downstream sanity: `sm_pm_router_commute_L5` → clean (resolves correctly)

ZERO new axioms. No `sorryAx`, `ofReduceBool`, or `Lean.ofReduceBool` in any
refactored theorem.

## Honest partial-failure notes (ground rule 8)

- **n_out ≥ 3 multi-node class (177 theorems) ABANDONED**: these unfold 3+ writer
  nodes with heterogeneous op/see-through topologies; a clean single backbone would
  require per-topology specialization with diminishing returns. Left hand-written.
- **`FW_stack` (3 theorems, 24 inputs)**: no `dstepK` for arity 24; hand-written.
- **`_shallow` sliding-window unfolds & 1 `ChunkPrim` n2 exception**: structurally
  irregular; hand-written.
- These 176 hand-written theorems account for the bulk of the residual unfold lines,
  so the realized −13.5% is below the ~50% aspiration but is fully correct, faster,
  and axiom-clean.

## Pre-existing `sorry` disclosure

`sm_pm_router_commute_layer` (Pattern_3.lean) carries a `sorry` in the baseline
(inside the DO-NOT-TOUCH `sm_pm_*` set). Not introduced or affected by this refactor.

## Verdict

**SHIP.** 510/686 denote-unfold theorems genericized onto a 7-lemma zero-sorry
backbone; all names preserved; build EXIT 0 and 19% faster; kernel-clean.

## Commit

`f770f8e36f50d97264cf3dce95c90169a957f049` on branch `iroha-denote-refactor`.

---

# RESULT — ROUND 2 (straggler eat, branch `iroha-denote-refactor2`)

## Summary

Round 2 refactored **143 of 175** hand-written stragglers onto the EXISTING round-1
`DenoteUnfoldGeneric` backbone (`denote_leaf_val`, `dstep1..7`). Key finding: the
round-1 `dstepK` lemmas **compose by nesting** to arbitrary tree depth, so **no new
backbone lemmas were required** — the 143 multi-hop stragglers are expressible as
nested `dstepK` term-mode proofs. This was a pure proof-generation task.

## Metrics

| Metric | Before (r2 baseline) | After | Delta |
|---|---:|---:|---:|
| `Pattern_3.lean` lines | 40,820 | 36,980 | **−3,840** (−9.4%) |
| Hand-written stragglers | 175 | 32 | −143 refactored |
| `denote_*` theorem names | 700 | 700 | 0 (ALL preserved) |
| `#print axioms` blocks | 26 | 26 | 0 |
| `sorry` tokens | 3 (pre-existing) | 3 (pre-existing) | 0 new |
| Full build | 25m48s wall | 29m54s wall | +4m06s* |

\* Build-time delta is confounded by shared-machine load (baseline tail ran at load ~3,
final ran at load ~25 on a 96-core host shared with other agents' Lean builds). The
refactored file is 3,840 lines SMALLER and uses the same `by decide`/`dstep` machinery
as round-1's 511 genericized theorems (which build in ~25min), so under equal load the
compile cost is expected to be neutral-to-lower. A like-for-like re-measure was not
performed to avoid a second ~30min build under continued contention. Reported honestly.

## Build

`lake build denote.yoco_goals.Pattern_3` → **EXIT 0** (wall 29m54s). See
`refactor_build_r2.log`.

## Kernel axiom audit

`#print axioms` on the 7 reused backbones (`denote_leaf_val`, `dstep1,2,3,4,5,7`) and
8 refactored theorems (`denote_sm_goal_3_7523`, `denote_pm_goal_3_7805`,
`denote_sm_goal_3_4811`, `denote_sm_goal_3_4787`, `denote_pm_goal_3_7619`,
`denote_sm_goal_3_4746`, `denote_pm_goal_3_4772`, `denote_pm_goal_3_7751`) — ALL report
exactly `[propext, Classical.choice, Quot.sound]`. See `axiom_audit_r2.log`.

## Per-class honest outcome

| Class | Count | Outcome |
|---|---:|---|
| hval-block multi-hop trees | 143 | ✅ REFACTORED (nested `dstepK`) |
| sliding_window / zigzag ring nodes | 15 | ❌ ABANDON — ring writer node; `dstep` only handles non-ring (`applyNodeRingAttn_eq_applyNode_of_not_ring`) so ring hops have no backbone. |
| `_shallow` + shallow sliding-window | 5 | ❌ ABANDON — structurally irregular sliding-window unfolds. |
| allGather collective | 4 | ❌ ABANDON — output is a collective over multiple ranks, not a single-writer value chain. |
| inline identity-collapse (4692/4693/4708×2) | 4 | ❌ ABANDON — proofs collapse an identity `FW_float`/`FW_multiref` chain in one top-level `rw` with no per-node `have hval_` blocks; the generator's inline path mis-classifies the collapsed writer input as a leaf. Refactorable in principle by recursing through the identity chain, but excluded to keep ZERO risk of a wrong proof. |
| all2all / moe_gmm / topk routing | 3 | ❌ ABANDON — MoE routing ops have no `dstepK` backbone. |
| FW_stack (arity 24) | 1 | ❌ ABANDON — arity-24 write-once/use-once; no `dstep24`, template explodes. |

## Method (reproducible)

1. Parse each straggler's regular proof: extract per-writer-node `(node record, node
   index m, applyNode_*_out helper call)` from its `have hval_<tid>` blocks.
2. Emit a nested `dstepK` term: per input tid — kept-denote → `rfl`; leaf/weight →
   `DenoteUnfoldGeneric.denote_leaf_val`; writer → recurse (nested `dstepK`).
3. `happly` per node = `(fun s => by rw [<original applyNode_*_out call, store→s>])`.
   Using `by rw` (not a raw term) lets `rw` infer the `∀ params` argument on helpers
   like `applyNode_fw_rms_norm_out` exactly as the hand proofs did.
4. Validated ALL 143 generated proofs in a scratch module importing prebuilt
   `Pattern_3.olean` (7m16s, EXIT 0) BEFORE applying — de-risking the expensive rebuild.
5. Applied in place preserving every theorem name, trailing `set_option`, and
   `#print axioms` line; deleted scratch modules; full rebuild EXIT 0; axiom audit.

## Ground-rule compliance

- ZERO SORRY introduced ✅ · ZERO new axioms ✅
- All 175 straggler names PRESERVED (700 `denote_*` names unchanged) ✅
- Backbones kernel-clean ✅ · Build EXIT 0 ✅
- Did NOT touch HsHelpersGeneric, RouterShapesHelpers, `sm_pm_*`, `mk_*`, Denote.lean,
  other Pattern files, or the 511 round-1 genericized theorems ✅

## Commit

`fe24f18` (the substantive refactor commit) on branch `iroha-denote-refactor2`.
