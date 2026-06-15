# FW_linear Goals 73 / 98 — Report

**Status:** ✅ DONE — both proved clean, committed `a4fbe3b` on `work-from-main-2026-06-12`.
**Acceptance:** verified post-hoc by 彩叶 on 2026-06-14 (worker PID 1666881 died right at the report-write step, commit had already landed).

## What these goals are

Last 2 of the 12 leftover FW_linear goals. Pattern: **replicated-X + ChunkPrim(dim2) on X + W gather + AllReduce**.

- X is replicated across 4 ranks (shape `[1,8,32]`).
- Each rank chunks X along dim2 (`chunkPrimDimN 2 4 r`) → local `[1,8,8]`.
- Weights `ws` (4× `[32,8]`) are col-parallel; PM gathers them via `allGatherPrimDimN 1 4 0` → `[32,32]`.
- LHS `fw_linear x (gather ws)` must equal `allReducePrim 4 0 (ofFn r => fw_linear (chunk x) (ws[r]))`.

Structurally like Goal_31 (AllReduce) but with **ChunkPrim nodes inside the PM graph**.

## New lemmas added to `denote/Denote.lean` (pure incremental, appended after `fw_linear_colParallel_4_1_8_32_128_8`)

1. **`allGatherPrimDimN1_4_valAt_32_8`** — `valAt` of the gathered `[32,32]` weight at `(row*32 + r*8 + lc)` reduces to `valAt ws[r] (row*8 + lc)`. Pure index arithmetic (omega).
2. **`fw_linear_colParallel_4_1_8_32_32_8`** — the `[32,8]` col-parallel bridge theorem (analogue of the existing `[32,128,8]` one), `set_option maxHeartbeats 2000000`.

No existing definition or theorem modified. `git diff 88b2d64..HEAD` = **446 insertions, 0 deletions**.

## Acceptance results

| Goal | `lake build` | `#print axioms` |
|------|--------------|-----------------|
| Goal_73 | EXIT 0 (951 jobs) | propext, Classical.choice, Quot.sound + denote whitelist (applyNode_fw_linear_out, erfFn, expFn, piScalar, scalarToNat, sqrtFn) |
| Goal_98 | EXIT 0 (951 jobs) | identical set |

- ❌ no `sorryAx`
- ❌ no `native_decide` / `Lean.ofReduceBool`
- ❌ no new/fake axiom
- ⚠️ only harmless `linter.unreachableTactic` warnings (one stray tactic each at line 134 — cosmetic, not closing anything).

Denote.lean change is pure-additive incremental. Clean.

## FW_linear leftover-12 final tally

All 12 leftover FW_linear goals now on `work-from-main-2026-06-12`:
- B-group 6× AllToAll (48/28/76/78/101/103)
- 手证 4× AllReduce inner-split (31/33/81/82)
- **这 2× chunk+AllReduce (73/98)** ← this report

→ FW_linear leftover batch **complete**.
