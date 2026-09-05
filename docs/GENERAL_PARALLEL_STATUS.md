# General parallel-configuration status

## Scope split

Parallel support is not one boolean:

- **TP:** ordinary linear/matmul/embedding/elementwise and collective relations;
- **CP/ring:** ordered token ownership, shuffle/unshuffle, packed sequence metadata, ring attention;
- **EP/MoE:** expert ownership, routing, all-to-all and full-expert boundaries;
- **DP:** reduction groups and optimizer-gradient reconstruction;
- **PP:** stage boundaries and composition authority.

A dynamic TP collective does not imply arbitrary CP/EP/DP/PP combinations.

## Existing evidence

The checked GPT-2 authority is already SM=1 / PM=4. Its ordinary forward path uses dynamic-K relation families. Therefore the previous statement “the project only supports TP=2” was false.

The first pure-TP fixed-rank boundary found on that authoritative ancestry was GPT Goal 107 `BW_sum` at compiler segment `segment_000188`. The previous matcher required exactly ranks `(0,1,2,3)`, the renderer required `k == 4`, and the Lean backend was a concrete four-shard theorem.

## Completed vertical slice: dynamic-K `BW_sum`

The boundary is now identified by:

```text
bw-sum-scalar-broadcast-dim2-k-rank
```

The compiler now derives `K` from the exact ordered PM writer list and accepts `K >= 2`, including non-power-of-two `K=3`. It validates:

- PM writer ranks are exactly `0..K-1`;
- every writer is binary `BW_sum`;
- the scalar gradient is one shared, pure-init singleton authority;
- all PM output shard shapes agree;
- SM/PM outputs form an exact equal-shard dim-2 reconstruction.

The renderer emits an exact `1+K` writer frame, dynamic `allGatherPrimDimN 2 K`, and no fixed rank-four backend identity.

The kernel theorem is:

```lean
TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3
```

It is list-based and proves arbitrary nonempty ordered `K`, for homogeneous rank-3 shards `[d0,d1,d2]` with positive gathered width `d2`. It does not assume a power of two or GPT's concrete `[1,8,32]` shard.

## Verification receipts

- Python matcher/renderer controls: K=2, K=3 and K=4, plus fail-closed mutations for rank, rank-3 theorem domain, input/output shape agreement, zero extents, parameters, and scalar reduction authority.
- Focused Python gate: `58 passed` across BW_sum, compound dispatch, registry and real GPT Goal 107 checks.
- Full influence gate: `510 passed in 3345.85s (0:55:45)`.
- Generic Lean theorem: `lake build denote.KRankBWSum` succeeded and materialized `denote/KRankBWSum.olean`.
- Exact renderer replay over real GPT Goal 107 segment `segment_000188` compiled successfully as a staged one-segment Lean module.
- The singleton and interleaved `FW_sum`/`BW_sum` compound dispatch paths both use the same dynamic-K theorem identity; the old rank-four backend is removed rather than retained as fallback.
- All canonical formal whole-model generations remained byte-identical:
  - GPT-2: 97 files, 1,968,291 bytes;
  - YOCO-MoE 0.4B: 2,832 files, 55,891,040 bytes;
  - YOCO-3B: 1,363 files, 37,377,383 bytes.

## Next pure-TP boundary

The next compiler position is `segment_000189`, `BW_linear` dX row reduction. It is still rank-four-specific and is coupled to several compound renderers. It must be generalized with a list-based matmul/reduction theorem and migrated as one rule/backend identity; deleting only the Python rank check would be unsound.

YOCO's two-rank zigzag/ring rules are a separate CP/EP topology problem and are not evidence that ordinary TP remains limited to two ranks.
