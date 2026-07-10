# BASELINE — hs_step% macro task

Branch: `iroha-hs-macro` (based on `main` @ 863cf1b)
Target file: `trainverify/denote/yoco_goals/Pattern_3.lean`
Toolchain: `leanprover/lean4:v4.31.0`, mathlib v4.31.0

## Pre-change state (HEAD 863cf1b)

- `Pattern_3.lean`: **40,820 lines**
- `RouterShapesHelpers.hs_*` theorems: **1116 total**
  - 1113 generic (delegating to `HsHelpersGeneric` backbone, ~11 lines each)
  - 3 hand-written non-generic: `hs_4714` (allGather), `hs_9655` / `hs_9656` (maybe_shuffle)
- hs_ generic block: ~12,450 lines
- Prior refactor (commit `5b8e8d8`) had already reduced these from ~18,735 lines
  to ~11,000+ by delegating to 5 backbone lemmas
  (`denote_leaf_shape`, `denote_step_1in`, `denote_step_id`,
  `denote_step_2in`, `denote_step_7in`).

## Baseline build

- `lake build denote.yoco_goals.Pattern_3` — EXIT 0
- Wall time (uncontended): **~25m13s** (reference from prior refactor build logs)

## Helper class census (1116 total)

| class | count | backbone lemma        | `(by decide)` count |
|-------|-------|-----------------------|---------------------|
| leaf  | 142   | denote_leaf_shape     | —                   |
| 1in   | 286   | denote_step_1in       | 6                   |
| id    | 366   | denote_step_id        | 6                   |
| 2in   | 273   | denote_step_2in       | 7                   |
| 7in   | 46    | denote_step_7in       | 12                  |
| hand  | 3     | (hand-written)        | —                   |
