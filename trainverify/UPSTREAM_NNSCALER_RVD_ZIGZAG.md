# nnScaler: RVD cannot express the layout `maybe_shuffle` produces

Found by TrainVerify while formally verifying YOCO-MoE-A0.4B (SM 1 GPU vs
PM 2 GPUs, `pcs/all2all_moe.yaml`). Reported as a **design limitation**, not a
coding slip — the code is doing the only thing the abstraction allows.

## Summary

A tensor that has passed through `wrap_maybe_shuffle` is sharded in zigzag
order. nnScaler's partition model cannot represent that, so the op annotates
itself as elementwise identity. Downstream, nnScaler believes the tensor is an
ordinary dim-0 split and inserts a plain `AllGatherPrim`, whose runtime is a
naive `torch.concat` over rank order. Concatenating zigzag shards does not
reconstruct the original sequence.

Result: for any tensor gathered while still inside the shuffled region, the
multi-GPU value differs from the single-GPU value.

## The chain

**1. The layout is inexpressible.** `nnscaler/graph/gener/rvd/layout.py`:

> This class assumes a full-tensor can only be uniformly partitioned /
> replicated on dimensions and values.

R(eplicate) / V(alue-split) / D(imension-split) only. `IRTensor` carries no
permutation or layout field.

**2. So the annotation must claim identity.**
`nnscaler/customized_ops/ring_attention/maybe_shuffle.py`:

```python
def maybe_anno(hidden_states, cu_seqlens, *args, **kwargs) -> str:
    return "l h, e^ -> l h"
```

**3. But the implementation really permutes.** `wrap_maybe_shuffle` →
`shuffle_varlen` → `_ShuffleVarlenA2A`, carrying `send_perm` / `recv_perm` /
`inv_send_perm` / `inv_recv_perm` over an `all_to_all`. Under cp=2 with L=8,
rank 0 ends up owning global positions `[0, 1, 6, 7]`, not `[0, 1, 2, 3]`.

**4. So the gather is wrong.** Believing the tensor is a plain dim-0 split,
nnScaler inserts `AllGatherPrim` (`nnscaler/ir/adapter/prim.py:426`), whose
signature is `nnscaler.runtime.adapter.all_gather`
(`nnscaler/runtime/adapter/collectives.py:92`):

```python
otensor = torch.concat(tuple(tensor_list), dim=dim)
```

Rank-order concat of zigzag shards yields `[0, 1, 6, 7, 2, 3, 4, 5]`, not
`[0 .. 7]`.

## Concrete instance

YOCO-MoE-A0.4B, `llm/arch/model.py`: `routing_map` / `expert_prob` are
collected inside the shuffle window, and `wrap_maybe_unshuffle` is applied only
to `h`. So `torch.stack(all_routing_map)` is gathered while still permuted.

In the traced PM graph, exactly two collectives consume zigzag data:

```
node 1897 AllGatherPrim ins=[11729, 11730] -> 4675   (all_routing_map)
node 1898 AllGatherPrim ins=[11781, 11782] -> 4676   (all_expert_prob)
```

Every other cross-rank node is either upstream of the shuffle or downstream of
the unshuffle. The loss heads (4673/4674) gather after `FW_maybe_unshuffle`
(nodes 1912/1913) and are correct.

This graph really does shuffle: `dp_sharded` defaults False so
`enable_ring=True`, and the shuffle input is dim-0 sharded
(`[2048, 1024]` of `[4096, 1024]`), which sends `emit_ring` down the
`partition_dims[0][0] == 0` branch and produces a 2-device `process_group`.

## Consequence

`all_routing_map` feeds the MoE balance loss in `nnscaler_train.py`. That
computation is outside the traced graph, so we have **not** verified an
end-to-end numerical impact and are not claiming one. What we can state is that
the tensor itself differs between the 1-GPU and 2-GPU runs, so any consumer
sensitive to row order sees different data. `loss_mask` and `tag_index` are
indexed by original token position, which suggests sensitivity, but confirming
that is a separate exercise.

## Possible directions

We have no strong preference, and each has costs we are not positioned to judge:

1. **Make the layout representable.** Add a permuted-shard concept to RVD, or a
   layout tag on `IRTensor`, so the adapter generator knows an ordinary gather
   is invalid and emits unshuffle-then-gather.
2. **Make the op honest at the annotation level.** If a shuffled tensor could be
   annotated as something other than elementwise identity, the existing
   machinery might refuse the naive gather on its own.
3. **Guard at adapter generation.** Cheapest: when the producer is a
   `maybe_shuffle` with a >1 process group, refuse to pair it with a plain
   `AllGatherPrim` and require an explicit unshuffle first.

## What we checked before filing

Compensation ruled out by reading, not inferring:

* `emit_ring` — computes `process_group` only, no reordering
* `shuffle_varlen` / `_ShuffleVarlenA2A` — genuinely permutes
* `RVDLayout` — no permutation concept
* `nnscaler/ir/tensor.py` — no layout/permutation field (zero grep hits)

To be explicit about scope: we verified this on one model and one 2-GPU plan.
We have not surveyed other CP configurations, and we may be missing context
about intended usage of `maybe_shuffle` that would change the picture.
