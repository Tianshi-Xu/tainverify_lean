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

## Suggested next step

Run the semantic witness in the other direction: instantiate the graph on a
concrete store where the zigzag ownership is observable (the
`ZigzagSemanticWitness.positions4` construction generalises) and evaluate both
sides of `goal_3` under `denoteGraphDistributedFaithful`. If they differ, that
is a machine-checked refutation of the generated goal, which is a more useful
artifact than a stuck proof.
