# goal_3 / goal_4: a layout split inside a single stack

**Status:** blocked, and I believe the block is real rather than a proof-effort
problem. Recording the evidence so the next pass does not re-derive it.

## What the two goals are

```
goal_3 = { ts := 4675, tsShape := [24, 4096, 64], tps := [{rank := 0, tid := 4675}] }
goal_4 = { ts := 4676, tsShape := [24, 4096, 64], tps := [{rank := 0, tid := 4676}] }
```

Both are 1-tp: the single PM tensor product is the PM graph's own
`AllGatherPrim … params := [1]`, i.e. a **dim-1** gather of the two per-rank
stacks. So the obligation is a plain value equality `SM t = PM t`.

* SM node 913 `FW_stack [4710, 4764, …, 5900] -> 4675` (24 members, each `[4096, 64]`)
* SM node 914 `FW_stack [4711, 4765, …, 5901] -> 4676`
* PM nodes 1887/1892 stack rank 0/1 into `11729`/`11730` (each `[24, 2048, 64]`)
* PM node 1897 `AllGatherPrim [11729, 11730] -> 4675 params := [1]`

## The commute lemma is done

`denote/StackGatherDim1.lean` (commit `e68aa6c9`, kernel triple only, no
`native_decide`):

```
fw_stack_allGather0_eq_allGather1_stack :
  fw_stack fulls = allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs]
```

given each `fulls[k] = allGatherPrimDimN 0 2 0 [as[k], bs[k]]`. That is exactly
the shape of the goal, so if all 24 members were ordinary dim-0 gathers, both
goals would close mechanically from here.

## Why they do not close

The 24 members are **not all in the same layout**. Splitting them by their
producing node against the CP2 shuffle (SM node 472, PM nodes 1003/1005):

| members | SM producer | layout on the faithful track |
|---|---|---|
| `4710 … 5304` (12) | nodes 27–456, **before** the shuffle | ordinary dim-0 gather |
| `5361 … 5900` (12) | nodes 523–908, **after** the shuffle | zigzag |

Confirmed by dataflow, not just node ordering: taking the transitive input
closure of the PM shard of a late member (`11625`) reaches shuffle output
`9655`; the closure of an early member's shard (`7483`) does not reach either
shuffle output at all.

The existing per-member faithful theorems agree with this split:

* early 12 → `recon_intermediateGoal_N_faithful : InitGoalHolds …` (ordinary gather)
* late 12 → `recon_zigzagGoal_N_faithful : Zigzag2Rel … [4096, 64] [2048, 64]`

`Zigzag2Rel` deliberately does **not** assert that the two exposed shards
ordinary-gather to the full tensor — `ZigzagLayoutRel.lean` says so in as many
words, and `ZigzagSemanticWitness.contiguous_rank0_ne_zigzag_rank0` exhibits a
concrete cp=2 counterexample (rank 0 owns global positions `[0, 3]`, not
`[0, 1]`).

So for the late 12 members, the hypothesis `fulls[k] = allGatherPrimDimN 0 2 0
[as[k], bs[k]]` that the commute lemma needs **is false as stated**, and the
goal as generated asserts an ordinary dim-1 gather over all 24 uniformly.

## Where the unshuffle is

The graph has exactly one unshuffle pair (PM nodes 1912/1913 → `11727`/`11728`),
and it sits at the very end, on the residual stream feeding the loss head. It is
*not* in the ancestry of the stacked routing tensors. So nothing in the graph
converts the late members back to contiguous layout before they are stacked.

## What this means

Two possibilities, and they should be distinguished before any Lean is written:

1. **The generated goal is wrong.** The emitter treated node 1897's dim-1
   `AllGatherPrim` as an ordinary reconstruction without noticing that 12 of the
   24 stacked rows are zigzag-owned. If so this is an upstream fidelity bug and
   the fix belongs in the emitter, not in a proof.
2. **The Python is doing something the Denote model does not see** — e.g. the
   routing tensors are gathered/unshuffled inside the stack op, or the
   per-layer router runs on contiguous input even after the shuffle.

Per the 2026-07-03 standing rule (upstream fidelity first), this needs a check
against the nnScaler/llm-train authority for what the per-layer routing map
ownership actually is at layers 12–23 before proving anything. Closing these two
goals with the ordinary-gather statement while the late members are genuinely
zigzag would be exactly the "downstream success over broken upstream" failure
mode the rule exists to prevent.

## Which reading is right: the emitter is shape-only

Settled by reading the emitter. `Verdict/graph_to_lean.py`:

```python
def _infer_gather_dim(ts_shape, tp_shape, num_pieces) -> int:
    """Infer which dimension was split by comparing SM and PM shard shapes."""
    for dim in range(len(ts_shape)):
        if tp_shape[dim] * num_pieces == ts_shape[dim]:
            ...
            return dim
    return 0
```

`gatherDim` and `replicated` are both derived **only** from shape arithmetic —
`tp_shape[dim] * num_pieces == ts_shape[dim]` and `tp_shape == ts_shape`. Nothing
in the goal emitter consults ownership, replica groups, or whether the tensor is
downstream of a `FW_maybe_shuffle`. `REPLICA_GROUP_OPS` (which does list
`FW_maybe_shuffle`/`FW_maybe_unshuffle`) is used for *node* replica metadata, not
for lineage-goal layout.

A zigzag shard and a contiguous shard have **identical shapes** (`[2048, 64]`
either way — that is the whole point of the `ZigzagSemanticWitness` shape-equal /
value-different counterexample). So the emitter cannot distinguish them even in
principle, and emits `gatherDim := 1, replicated := false` for `goal_3`/`goal_4`
regardless of the fact that 12 of the 24 stacked rows are zigzag-owned.

This is reading **1**: the generated goal is wrong, and it is an upstream emitter
bug rather than a missing proof. The same blind spot presumably affects any other
goal whose shards are zigzag-owned but shape-identical; `goal_3`/`goal_4` are
simply where it became load-bearing, because the stack forces all 24 members into
one uniform statement.

## Status update: emitter fixed (commit `8ae7f544`)

The fix landed in `Verdict/graph_to_lean.py`. Ownership is now recovered
structurally rather than guessed from shapes:

> a tid is zigzag-owned iff its backward dataflow closure reaches a
> `FW_maybe_shuffle` output without being stopped by a `FW_maybe_unshuffle`
> output.

Goals whose own `tps` are zigzag-owned are suppressed: an explanatory comment
replaces the `def`, the name is dropped from `obsTids` / `goals` / prereq lists
so the module still builds, and a loud summary is printed at generation time
saying they are **not covered**.

### What changed on a real regeneration

Running `scripts/regenerate_yoco_a04b.py` against the archived authority pkls:

* 507 goals suppressed, including `goal_3` and `goal_4`
* `goal_1`, `goal_2`, `goal_5` survive
* graph node lines (2829), shape entries (8611) and all 359 `initGoal`s are
  **byte-identical** to the checked-in version — the change is confined to the
  goal set

### Cross-check against existing proofs

Of the 505 suppressed intermediate goals:

* **0** had a faithful `InitGoalHolds` proof
* 502 were proven only as `Zigzag2Rel` — exactly the relation the emitter now
  says cannot be restated as an ordinary gather
* 3 had no faithful theorem at all

So the suppression contradicts nothing that was already proven. The `Zigzag2Rel`
proofs remain valid and are now the *only* claim made about those tensors, which
is the correct state of affairs.

### One correction to my own reasoning

An earlier draft of the gate also suppressed goals *transitively*, on the theory
that losing a prereq makes a goal "look provable but not be". That is backwards:
dropping a hypothesis makes a statement **stronger**, not false. It was also
empirically wrong — it flagged `goal_1`/`goal_2`, which are machine-checked in
`L23FaithfulLossGoals.lean`. Their PM tensors sit *after* the graph's
unshuffle, so they are contiguous and their statements are true even though
their ancestry is full of zigzag tensors. The rule now fires on a goal's own
`tps` only, and a regression test pins that.

Where a prereq is genuinely dropped, the emitter leaves a `-- NOTE:` marking the
resulting goal as stronger than generated, so the weakening is visible rather
than silent.

### Where goal_3 / goal_4 stand now

They are correctly reported as open rather than emitted as false statements.

The zigzag-aware goal form now exists and is emitted:
`ZigzagLineageGoal` / `ZigzagGoalHolds` (commits `27bc69fc`, `9e4182b7`) carry
the cu tid and discharge against `Zigzag2Rel`. On YOCO-MoE, 505 of the 507
suppressed goals are re-emitted in that true form. `goal_3`/`goal_4` are the
remaining two: they are 1-tp `AllGatherPrim`s, so they have no two-shard zigzag
form yet.

The dim-0→dim-1 stack/gather commute lemma remains landed and correct
(`fw_stack_allGather0_eq_allGather1_stack`, kernel triple only); it will be
directly reusable once those two can be stated truthfully.

## The blast radius: hand-written proofs were consuming the bug

Removing the false goals surfaced something more serious than the goals
themselves. `Pattern_4` derived, for 12 of its 24 stacked members:

```lean
have hb_5359 : initSM 5359 = allGatherPrimDimN 0 pm_goal_4.numRanks 0
    [initPM 9729, initPM 9730] :=
  extract_dual intermediateGoal_5359 ...
```

Those 12 tids are **exactly** the post-shuffle members identified independently
by dataflow closure. Two unrelated routes to the same partition. `Pattern_1` had
3 more. The step only typechecked because the emitter *published*
`intermediateGoal_5359` as an ordinary-gather goal — the proof was consuming the
emitter's bug as a hypothesis.

**Nothing unsound was ever concluded**, and the reason is worth recording:

1. Patterns target `goal_N_stmt_cut`, over the **sliced** graph. `pm_goal_3` /
   `pm_goal_4` are built from `ChunkPrim` and contain no shuffle, so the
   cut-level statements are true.
2. The cut→full lift never existed. Only `Goal_5_CutToFull.lean` was ever
   emitted, and `Instances.prove_goal_{3,4}_from_pattern_{3,4}` was `sorry`.

That `sorry`, which read as a mundane emitter limitation ("non-base cut_to_full
bridge missing"), was load-bearing: it was the only thing standing between a
false goal and a claimed proof.

The repair lifts the assumption to an explicit hypothesis parameter
(`ZigzagCutGatherHyp`) rather than deleting the step or re-deriving it, so the
dependency is visible instead of silently inherited. Details in
`PATTERN_4_ZIGZAG_DEPENDENCY.md`.

`ZigzagReconstruction.lean` needed a different treatment: all 90 of its theorems
are stated over `denoteGraph_ringAttn`, which models the shuffle as identity
(AGENTS #24 — shape-correct, value-lossy for cpSize > 1). On that track the
ordinary-gather record is the correct statement, so its 12 goal records are
re-declared module-locally rather than published globally, where they could be
mistaken for faithful-track goals.

