# Pattern_4 depended on the false ordinary-gather assumption

Recorded 2026-07-28, after the CP-zigzag ownership gate landed.

## What surfaced

`Pattern_4.lean` proves `goal_4_stmt_cut` and, to do so, unpacks all 24 stacked
per-layer routing members via `extract_dual`, deriving for each one:

```lean
have hb_5359 : initSM 5359 = allGatherPrimDimN 0 pm_goal_4.numRanks 0
    [initPM 9729, initPM 9730] :=
  extract_dual intermediateGoal_5359 ...
```

That is exactly the ordinary dim-0 gather claim. Of the 24 members it unpacks,
**12 are zigzag-owned**:

```
5359 5408 5457 5506 5555 5604 5653 5702 5751 5800 5849 5898
```

These are precisely the layer-12..23 members produced after the CP2
`FW_maybe_shuffle` — the same 12 identified independently by dataflow closure in
`GOAL_3_4_LAYOUT_SPLIT.md`. Two independent routes to the same partition is
strong evidence the split is real.

## Why this matters

`ZigzagGoalRefutation.gatheredZigzag_ne_full` machine-checks that an ordinary
dim-0 gather of zigzag shards does **not** equal the contiguous tensor (same
shape, disagreeing at flat index 2: 6 versus 2). So `hb_5359` and its eleven
siblings assert something false about the full graph.

They were derivable only because `intermediateGoal_5359` etc. *existed* as
generated ordinary-gather goals — i.e. Pattern_4 was consuming the emitter's bug
as a hypothesis. With those goals no longer emitted, the derivation correctly
fails to typecheck.

This is the healthy outcome. The proof did not break; it stopped being able to
assume a falsehood.

## Why nothing unsound was ever *concluded*

Two containment facts, both checked:

1. `Pattern_4` targets `goal_4_stmt_cut`, over the **sliced** graph. `pm_goal_4`
   is built from `ChunkPrim` and contains no shuffle at all, so the cut-level
   statement is sound.
2. The lift from cut to full never existed. There is no `Goal_4_CutToFull.lean`
   (only `Goal_5_CutToFull.lean` was ever emitted), and
   `Instances.prove_goal_4_from_pattern_4` was `sorry` from the start.

So the false full-graph statement was never discharged. The `sorry` that looked
like an emitter limitation ("non-base cut_to_full bridge missing") was in fact
load-bearing: it was the only thing standing between a false goal and a claimed
proof.

## Current state

`Pattern_4`'s 12 zigzag `extract_dual` steps do not compile against the corrected
goal set, and should not be patched to compile. Making them work again would
require re-introducing the false hypothesis.

The honest repair is to restate those 12 members against `Zigzag2Rel` — the
`ZigzagLineageGoal` form now emitted for them — and route the stack through
`ZigzagGoalHolds.to_gather_after_unshuffle`, which converts a zigzag goal into a
genuine `Gather2Rel` once the unshuffle has been applied. The stack/gather
commute lemma needed downstream is already proven
(`fw_stack_allGather0_eq_allGather1_stack`, kernel triple only).

That is a real proof effort on 12 members, not a mechanical fix, and it is the
remaining work for goal_4. Until it lands, goal_4 is **not covered** — which is
what the emitter now reports.
