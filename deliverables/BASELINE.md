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

---

# BASELINE — ROUND 2 (straggler eat, branch `iroha-denote-refactor2`)

- Branch: `iroha-denote-refactor2` (base `main` @ 863cf1b = round-1 merge)
- Target file: `trainverify/denote/yoco_goals/Pattern_3.lean`
- Toolchain: `leanprover/lean4:v4.31.0` (pinned)

## Pre-round-2 metrics

| Metric | Value |
|---|---|
| `Pattern_3.lean` line count | **40,820** |
| Round-1 genericized `denote_*` theorems | 511 |
| Hand-written stragglers remaining | **175** |
| Baseline full build (`lake build denote.yoco_goals.Pattern_3`) | **25m48s** (wall), EXIT 0 |
| `Pattern_3.olean` | ~46.4 MB |

## Straggler classification (175 hand-written)

| Class | Count | Round-2 plan |
|---|---:|---|
| hval-block multi-hop trees (ops covered by dstep1..7) | 143 | REFACTOR via nested dstep |
| sliding_window / zigzag ring nodes | 15 | ABANDON (ring op breaks dstep) |
| `_shallow` + shallow sliding-window variants | 5 | ABANDON (irregular) |
| allGather collective | 4 | ABANDON (no single-writer chain) |
| inline identity-collapse (4692/4693/4708×2) | 4 | ABANDON (identity float/multiref collapse; generator inline path mis-classifies writer inputs) |
| all2all / moe_gmm / topk routing | 3 | ABANDON (no dstep backbone for MoE routing) |
| FW_stack (arity 24) | 1 | ABANDON (24-in template explodes) |

## Note on baseline build timing

Baseline (25m48s) finished partly during a load-dip (load avg fell to ~3 near the tail);
the final round-2 build ran under load avg ~25. Wall-clock comparison is therefore
confounded by heavy shared-machine contention (this is a shared 96-core host).

## Pre-existing `sorry` (NOT introduced by round 2)

Still exactly the round-1 pre-existing `sorry` inside `sm_pm_router_commute_layer`
(a DO-NOT-TOUCH `sm_pm_*` theorem). `grep -c sorry` = 3 in BOTH the pre-round-2 file
and the post-round-2 file — round 2 introduced ZERO new `sorry`.
