# BASELINE — denote-unfold generic-lemma refactor

- Branch: `iroha-denote-refactor` (base `main` @ fb88c31; prior hs_ refactor @ 5b8e8d8)
- Target file: `trainverify/denote/yoco_goals/Pattern_3.lean`
- Toolchain: `leanprover/lean4:v4.31.0` (pinned)

## Pre-refactor metrics

| Metric | Value |
|---|---|
| `Pattern_3.lean` line count | **47,168** |
| `denote_{sm,pm}_goal_3_<tid>` value-unfold theorems | **686** (unique names) |
| Baseline full build (`lake build denote.yoco_goals.Pattern_3`) | **31m17s** (real), EXIT 0 |
| `Pattern_3.olean` | ~55 MB |

## Theorem classification (by count of `applyNode_*_out` steps in proof)

| Class | n_out | Count | Refactor plan |
|---|---|---:|---|
| clean single-node | 1 | 336 | genericize (n1) |
| see-through (target + 1 multiref passthrough) | 2 | 181 | genericize (n2) |
| multi-node | ≥3 | 177 | ABANDON (heterogeneous) |

Sub-cases left hand-written: 3 `FW_stack` (24-input), a handful of `_shallow` sliding-window
deep-unfolds, and 1 `ChunkPrim` n2 exception.

## Baseline axiom sanity

Sampled `denote_*_goal_3_*` names + downstream `sm_pm_*` all report
`[propext, Classical.choice, Quot.sound]`.

### Pre-existing `sorry` (NOT introduced by this refactor)

`sm_pm_router_commute_layer` (Pattern_3.lean:19277) contains `sorry` in the baseline.
It is inside the DO-NOT-TOUCH `sm_pm_*` set and is disclosed here for honesty.
