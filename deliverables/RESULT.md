# RESULT — Pattern_3 hs_ helper generic-lemma refactor

## Verdict: ✅ LANDED (full success, zero sorry, zero new axioms)

## What was done
Added a new `HsHelpersGeneric` namespace (5 backbone lemmas) to `Pattern_3.lean`
immediately before `namespace RouterShapesHelpers`, then rewrote **1113 of 1116**
`hs_<tid>` helpers to short invocations of those generics. All 1116
`RouterShapesHelpers.hs_<tid>` NAMES preserved exactly — downstream call sites
(`sm_pm_router_commute_L0..L9`, `mk_router`) build unchanged.

### The 5 generic lemmas (spike pattern, proven zero-sorry)
1. `denote_leaf_shape` — leaf init tids (no writer node) → `StoreShapesHold`.
2. `denote_step_1in` — 1-input value propagation (`f : Tensor → Tensor`): view, float,
   sigmoid, topk_routing, chunk, norm_linear, etc.
3. `denote_step_id` — 1-input identity passthrough (float/multiref/to).
4. `denote_step_2in` — 2-input propagation (add, mul, rms_norm, ...).
5. `denote_step_7in` — n-ary (all2all_moe_gmm_full, 7 inputs). Subsumes 1in/2in;
   1in/2in kept as cheaper-to-call specializations.

### 3 helpers intentionally left hand-written (per ground rule 8)
- `hs_4714` (allGather — single occurrence, no generic class)
- `hs_9655`, `hs_9656` (maybe_shuffle — 2 occurrences, no generic class)
These retain original hand-written proofs; not worth a dedicated generic.

## Metrics

| Metric | Baseline | Refactored | Delta |
|---|---|---|---|
| Total file lines | 54,496 | 47,167 | **−7,329 (−13.4%)** |
| Helper-block body lines saved | — | — | ~7,508 |
| `hs_<tid>` theorems | 1116 | 1116 | 0 (names preserved) |
| Helpers via generics | 0 | 1113 | +1113 |
| `Pattern_3` module build | 1447s | 1462s | +15s (+1.0%, noise) |

Build: `lake build denote.yoco_goals.Pattern_3` → **EXIT 0** (24:24 wall).
No build regression (well within the ±5% budget).

## Kernel audit (`#print axioms`)
All sampled = `[propext, Classical.choice, Quot.sound]` (standard, kernel-clean):
- Generics: `denote_leaf_shape`, `denote_step_1in`, `denote_step_id`,
  `denote_step_2in`, `denote_step_7in` ✓
- Helpers: hs_4680 (leaf), hs_4681 (float/id), hs_4701 (view), hs_4703 (add/2in),
  hs_4719 (sigmoid), hs_4733 (mul/2in), hs_7479 (chunk), hs_7483 (topk/1in),
  hs_7491 (moe/7in) ✓

## Downstream
`sm_pm_router_commute_L0 .. L9` and all `mk_router` invocations reference
`RouterShapesHelpers.hs_<tid>` by preserved name and build clean in the same
module (covered by the EXIT-0 full build).

## Honest notes
- Net line saving 7,329 (target was <11,000 saved, no regression >5%): ✅.
- Compile time essentially unchanged (+1%) as predicted — dominant cost is the
  per-helper `by decide` over the ~903-node graph, unchanged by the refactor.
- Sub-2000-line aspiration (metaprogramming macro) remains out of scope.

## Commit
SHA: 4751490484b42473bab19a9bb248ce5b61bb5fcd (branch `iroha-hs-refactor`, pushed to `origin`)
