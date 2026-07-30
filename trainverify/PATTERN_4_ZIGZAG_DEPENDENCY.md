# Pattern_4 and the 12 post-shuffle cut boundaries

Recorded 2026-07-28; corrected after the ownership-aware emitter landed.

## What surfaced

`Pattern_4.lean` proves the **shuffle-free sliced graph** statement
`goal_4_stmt_cut`. To assemble its 24-layer routing stack it needs ordinary
dim-0 gather relations for 24 boundary tensors. Twelve correspond to values
that are zigzag-owned in the faithful full graph:

```
5359 5408 5457 5506 5555 5604 5653 5702 5751 5800 5849 5898
```

The old emitter published those tids globally as ordinary-gather
`intermediateGoal_N`s. That is false on the faithful full graph: nnScaler's RVD
model cannot represent the permuted post-shuffle layout, so its runtime
AllGatherPrim is a rank-order concat that does not undo the zigzag. See
`GOAL_3_4_LAYOUT_SPLIT.md` for the audited source and executable reproduction.

Removing the false globals correctly broke Pattern_4's old `extract_dual`
derivations. Pattern_1 had the same issue for three boundaries: 5893, 5895,
5898.

## The cut graph is different

The relations are nevertheless valid **boundary contracts of the cut graph**.
`pm_goal_4` is a sliced graph built from `ChunkPrim`; there is no shuffle in the
cut. Its caller supplies contiguous shards, and the ordinary gather relation is
sound and satisfiable there.

The repair therefore does not reintroduce the globals and does not assume a
universal `ZigzagCutGatherHyp`. Instead:

* `Goal_4.lean` re-declares 12 local `goal4CutIntermediateGoal_*` records;
* `Goal_1.lean` re-declares 3 local `goal1CutIntermediateGoal_*` records;
* each list is appended to the corresponding `goal_N_cut_initGoals`;
* Pattern_1 / Pattern_4 extract the concrete relations from their existing
  `hInit : InitGoalsHold ...` packages, exactly like other cut boundaries;
* the existing zero-store joint witnesses prove those enlarged packages are
  satisfiable.

Thus the top-level cut theorem remains unconditional on any new layout
hypothesis, and its non-vacuity witness covers the contracts. The local names
cannot be mistaken for faithful full-graph goals.

## Containment

No false full-graph theorem was concluded:

1. Pattern_4 targets only `goal_4_stmt_cut`.
2. There is no `Goal_4_CutToFull.lean`.
3. The old `Instances.prove_goal_4_from_pattern_4` full-graph bridge was a
   `sorry`; after the false full statement was removed, the instance now exposes
   only the sound cut statement.

The full-graph `goal_3` / `goal_4` equalities remain two reported findings, not
proof obligations that can honestly be closed.
