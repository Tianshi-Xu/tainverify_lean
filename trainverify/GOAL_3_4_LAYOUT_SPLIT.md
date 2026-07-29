# goal_3 / goal_4: an RVD expressiveness gap in nnScaler

**Status:** both goals are FALSE as generated. Not provable, and correctly no
longer emitted. This file records the audited root cause.

**History note.** Earlier revisions of this document gave two different, WRONG
explanations. Both are corrected below, and the wrong versions are stated
explicitly so nobody re-derives them.

## What the two goals are

```
goal_3 = { ts := 4675, tsShape := [24, 4096, 64], tps := [{rank := 0, tid := 4675}] }
goal_4 = { ts := 4676, tsShape := [24, 4096, 64], tps := [{rank := 0, tid := 4676}] }
```

Both are the stacked per-layer MoE routing outputs (`all_routing_map` /
`all_expert_prob` in `llm/arch/model.py`).

* SM node 913/914 `FW_stack` of 24 members, each `[4096, 64]`
* PM nodes 1887/1892 stack rank 0/1 into `11729`/`11730`, each `[24, 2048, 64]`
* PM node 1897/1898 `AllGatherPrim [11729, 11730] -> 4675` with `params := [1]`

Node 1897 is a **real nnScaler node**, not something the emitter synthesised.

## Root cause: nnScaler's RVD model cannot express a permuted sharding

`nnscaler/graph/gener/rvd/layout.py`:

> This class assumes a full-tensor can only be **uniformly partitioned /
> replicated** on dimensions and values.

R(eplicate) / V(alue-split) / D(imension-split). There is no representation for
"sharded, but the rows are permuted across ranks", and `IRTensor` carries no
layout or permutation field (grep for `permut` / `layout` in
`nnscaler/ir/tensor.py`: zero hits).

Consequently `wrap_maybe_shuffle` can only annotate itself as elementwise
identity — `nnscaler/customized_ops/ring_attention/maybe_shuffle.py`:

```python
def maybe_anno(hidden_states, cu_seqlens, *args, **kwargs) -> str:
    return "l h, e^ -> l h"
```

while its implementation genuinely reorders `l` across ranks:
`shuffle_varlen` → `_ShuffleVarlenA2A` carrying `send_perm` / `recv_perm` /
`inv_send_perm` / `inv_recv_perm` over an all_to_all. Under cp=2, rank 0 ends
up owning global positions `[0, 1, 6, 7]`, not `[0, 1, 2, 3]`.

Because the annotation claims identity, nnScaler treats the post-shuffle tensor
as an ordinary D-split and inserts a plain `AllGatherPrim` when it needs the
full tensor. At runtime that is
`nnscaler/runtime/adapter/collectives.py::all_gather`:

```python
otensor = torch.concat(tuple(tensor_list), dim=dim)
```

a naive rank-order concatenation. Concatenating zigzag shards gives
`[0, 1, 6, 7, 2, 3, 4, 5]`, which is not the single-machine `[0 .. 7]`.

So the generated equality is false.

## Why goal_1 / goal_2 are unaffected

Position of the gather relative to the unshuffle:

```
PM 1912/1913  FW_maybe_unshuffle -> 11727/11728
PM 1918/1919  AllGatherPrim      -> 4673/4674     <- AFTER unshuffle: fine
PM 1897/1898  AllGatherPrim      -> 4675/4676     <- BEFORE unshuffle: broken
```

The residual stream `h` is unshuffled before its loss-head gather, so its shards
are contiguous by then. The routing tensors are stacked and gathered while still
inside the shuffled region, because `model.py` collects `routing_map` inside the
shuffle window and `wrap_maybe_unshuffle` is applied only to `h`.

## Two earlier explanations that were WRONG

**Wrong #1: "the 12 members produced after the shuffle are zigzag, the other 12
are not, so the stack is inhomogeneous."**

The inhomogeneity is real but is not the reason, and the framing misled the
gate. Both graphs contain `FW_maybe_shuffle` — the op is emitted
unconditionally. They differ only in `params := [cpSize, cpRank]`:

```
SM node 472 : params := [1, 0]
PM node 1003: params := [2, 0]
PM node 1005: params := [2, 1]
```

and `fw_maybe_shuffle_collective` short-circuits with
`if cpSize = 1 then localTensor`. The discriminator is **cpSize**, not the
presence of a shuffle. Testing for presence alone would flag every tensor in a
single-device graph, where ordinary gather is perfectly correct.

**Wrong #2: "balance loss multiplies `all_routing_map` by a position-indexed
`loss_mask`, so the mask is misaligned — llm-train has a bug."**

Retracted entirely. `4675` has **no consumer in either graph** — it is a leaf
output. The balance-loss computation (`* loss_mask`, `sum(dim=1)`, `bmm`) lives
in `nnscaler_train.py`, outside the traced graph, and is not part of any goal.
Reasoning about code outside the verification scope to conclude a goal inside it
is false was a methodological error. `llm/arch/model.py` uses the API correctly
and is not at fault.

## Attribution

| layer | verdict |
|---|---|
| llm-train (`model.py`) | not at fault, uses the API as intended |
| nnScaler | RVD expressiveness gap: `maybe_shuffle`'s real layout is inexpressible |
| Verdict emitter | faithfully reflects the nnScaler graph |

This is a **design limitation**, not a coding slip. Report it upstream as such.
Compensation was ruled out by reading `emit_ring` (computes `process_group`
only, no reordering), `shuffle_varlen` (genuinely permutes), and `RVDLayout`
(no permutation concept).

## Blast radius: exactly two nodes, and cp really is > 1

Both open questions from the first pass are now closed.

**The shuffle genuinely fires on this graph.** `gen_args.json` records
`pm: {plan_ngpus: 2, runtime_ngpus: 2, tp: 2}`, and `dp_sharded` defaults to
`False` (`llm/arch/config.py:57`), so `enable_ring = not dp_sharded = True`.

`wrap_maybe_shuffle` still early-returns unless `len(process_group) > 1`, and
`process_group` is chosen by `emit_ring` from the input's partitioning:

```python
partition_dims = [(i, f // s) for i, (s, f) in
                  enumerate(zip(sub_input.shape, full_input.shape)) if s != f]
if partition_dims[0][0] == 0:
    num = partition_dims[0][1]
    ...  process_group = <num devices>
elif partition_dims[0][0] == 1:
    process_group = None     # <- no shuffle
```

The shuffle input is sharded on dim 0:

```
PM 13257 / 13258: [2048, 1024]      SM 8011: [4096, 1024]
partition_dims = [(0, 2)]  ->  dim-0 branch, num = 2
```

So `process_group` has 2 devices, `shuffle_varlen` really runs, and cpSize = 2.
This also confirms the emitter's `cpSize = num_parts` assumption is correct
*here* — but note it is an assumption: `emit_ring` would pick
`process_group=None` for a dim-1 partitioned input, where `num_parts` would
still be 2. On a model that partitions the shuffle input on dim 1, the emitted
`params` would overstate cpSize.

**Only two collectives consume zigzag data.** Enumerating every cross-rank node
in the PM graph and testing each input for zigzag ownership:

```
node   26 AllReducePrim  ins=[7391, 7392]   -> 4680
node   55 AllGatherPrim  ins=[7445, 7446]   -> 4698
node  108 AllGatherPrim  ins=[7491, 7492]   -> 4714
node  111 AllGatherPrim  ins=[7545, 7546]   -> 4729
node  150 AllGatherPrim  ins=[7631, 7632]   -> 4752
node 1004 AllGatherPrim  ins=[14597, 14599] -> 11917
node 1897 AllGatherPrim  ins=[11729, 11730] -> 4675   <-- ZIGZAG
node 1898 AllGatherPrim  ins=[11781, 11782] -> 4676   <-- ZIGZAG
node 1918 AllGatherPrim  ins=[11837, 11838] -> 4673
node 1919 AllGatherPrim  ins=[11839, 11840] -> 4674
```

Exactly `goal_3` and `goal_4`. Node 1004 sits right after the shuffle but is
fed by the *other* branch of a `FW_multiref` (`9625 -> [14597, 13257]`), i.e.
the pre-shuffle value, so it is unaffected. Nodes 1918/1919 are the loss heads,
downstream of the unshuffle.

The impact on this model is therefore fully bounded: two goals, no more.

## What TrainVerify does now

`Verdict/graph_to_lean.py` suppresses goals whose PM tensors are zigzag-owned,
where "zigzag-owned" means: the backward dataflow closure reaches the output of
a `maybe_shuffle` **with cpSize > 1**, without being stopped by a
`maybe_unshuffle` output. Where a two-shard form exists the true obligation is
re-emitted as a `ZigzagLineageGoal` (discharged against `Zigzag2Rel`); 505 of
507 on this model. `goal_3`/`goal_4` are 1-tp and have no two-shard form, so
they are reported as **not covered** and counted as open.

Suppressing them without also reporting them would inflate coverage by shrinking
the denominator, which is the failure mode the "upstream fidelity first" rule
(2026-07-03) exists to prevent.

## Remaining uncertainty

Not verified: whether production training actually runs with cp > 1
(`enable_ring=not dp_sharded`), and what else in the model touches a tensor that
is gathered inside the shuffled region. Both are worth checking before filing
upstream.
