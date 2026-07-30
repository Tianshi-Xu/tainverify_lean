# YOCO-MoE faithful coverage (ownership-aware)

Updated 2026-07-28 after correcting the lineage emitter for CP zigzag ownership.
This replaces the old `1133/1156 (98%)` / `1135/1156` counts, which mixed
ordinary-gather and zigzag-layout obligations under one statement type.

## Total denominator

The original generated corpus has **1156 obligations**:

* 1151 intermediate tids
* 5 top-level goals

The denominator has NOT been shrunk. False/inexpressible goals remain visible as
findings rather than disappearing from coverage.

## Current classification

| class | total | faithfully proven | remaining |
|---|---:|---:|---:|
| ordinary contiguous ownership | 649 | 647 | 2 |
| CP zigzag ownership (`Zigzag2Rel`) | 505 | 502 | 3 |
| discovered false equalities | 2 | 0 | 2 findings |
| **total** | **1156** | **1149** | **7** |

Overall per-goal faithful coverage: **1149 / 1156 = 99.39%**.

**This is NOT an end-to-end theorem count.** A per-goal theorem may carry
caller-supplied value/layout hypotheses (`hValues`, `hCu`, `hx0`, etc.). The
cut-tier Pattern_1 / Pattern_4 chain no longer relies on an unconstrained
`ZigzagCutGatherHyp`: the 15 relations are local `cutIntermediateGoal_*`
boundary contracts included in the shuffle-free cut graphs' `InitGoalsHold`
packages, and the existing zero-store joint witnesses establish satisfiability.
Still, quote 99.39% only as per-goal faithful coverage; `Instances.lean` retains
cut→full `sorry`s for goals 1/2 and a raw cut-level `sorry` for goal 3 because
Pattern_3 proves only the honest conditional `goal_3_stmt_with_pins`. Goal 4's
sound cut instance is sorry-free; the false full-graph statements do not exist.

### Ordinary class

646 generated ordinary intermediate goals + 3 sound top-level goals
(`goal_1`, `goal_2`, `goal_5`) = 649.

* 644 / 646 intermediate goals have exact
  `recon_intermediateGoal_<tid>_faithful` theorems.
* all 3 sound top-level goals have faithful proofs.
* missing ordinary intermediates: tids **5928**, **5930**.

Note: top-level `goal_5` also concerns tid 5928. Its top-level proof does not
silently count as the missing intermediate theorem; these are separate members
of the original 1156-obligation corpus.

### Zigzag class

505 generated `ZigzagLineageGoal`s, of which 502 have exact
`recon_zigzagGoal_<tid>_faithful : Zigzag2Rel ...` theorems.

Missing zigzag intermediates: tids **5338**, **5340**, **5342**.

### False findings

Top-level `goal_3` / `goal_4` (tids 4675/4676) asserted ordinary equality after
nnScaler gathered still-zigzag-owned routing tensors with a rank-order
`torch.concat`. They are false on the audited CP2 graph and are not proof
obligations that can honestly be closed.

They stay in the denominator as two discovered counterexamples. See:

* `GOAL_3_4_LAYOUT_SPLIT.md`
* `UPSTREAM_NNSCALER_RVD_ZIGZAG.md`

## Reproduction method

Run:

```bash
python3 scripts/count_yoco_faithful_coverage.py
```

The script derives the counts mechanically from the checked-in source:

1. Parse `GeneratedYOCOMoE.lean` for ordinary `intermediateGoal_N`, emitted
   `intermediateGoal_N_zigzag`, top-level ordinary goals, and suppressed top
   goals.
2. Parse `denote/yoco_goals/*.lean` for exact theorem names
   `recon_intermediateGoal_N_faithful`, `recon_zigzagGoal_N_faithful`, and
   top-level faithful proofs.
3. Intersect by tid; do not count theorem-name substrings, ringAttn proofs,
   cut-graph pattern proofs, or stale declarations.

This classification deliberately excludes `denoteGraph_ringAttn`: that evaluator
models shuffle as identity and is shape-correct but value-lossy at cpSize > 1.
Only faithful-track results count.
