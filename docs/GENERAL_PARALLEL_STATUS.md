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

## Completed vertical slice: dynamic-K `BW_linear` dX

Goal 107 `segment_000189` now uses `bw-linear-dx-row-reduction-k-rank` and
`bw_linear_dx_allGatherPrimDimN_dim2_rank3`. K is arbitrary and nonempty, but
this theorem deliberately retains local gradient `[1,8,32]` and weight
`[32,32]`. Other dX layouts remain on their checked legacy rules.
The actual Goal 107 segment source was compiled and axiom-audited separately;
canonical GPT targets `(2,3,48)` do **not** cover Goal 107.

## Completed vertical slice: dynamic-K `BW_layernorm` dX

Rule: `bw-layernorm-dx-dim1-k-rank`.
Theorem: `bw_layernorm_dx_allGatherPrimDimN_dim1_3d` in
`denote/KRankBWLayernorm.lean`.

The ordered gradient/activation lists have length K. Local shapes are `[b,s,d]`,
full shapes `[b,s*K,d]`, with positive K,b,s,d and shared singleton gamma/beta.
The proof transports the actual row-local backward values, including both
row sums, through the rank/local-index gather map. It does not duplicate a
fixed-rank theorem. Width `d=1` preserves the parser's singleton **reduction**
parameter authority; other widths use singleton sharded authority.

Matcher, typed payload, transition digest, exact writer footprint, singleton
renderer, compound dX caller, and import selection use the new identity.
The triple renderer still requires K=4 and `[1,2,32]` because dgamma/dbeta remain
on their checked rank-four reduction theorems; this is not full backward
LayerNorm generalization.

Incremental evidence for this slice:

- `101 passed in 13.59s`: new controls, actual GPT Goal 107 integration,
  BW_sum/dX regression, registry/compound/import policy, and incremental selector.
- New theorem and committed K=3 / `[2,3,7]` generated witness built via Lake.
- Extra exact-source witnesses compiled for K=5 / `[2,3,7]`, K=3 / `[2,3,1]`,
  K=1 / `[1,1,1]`, and the retained rank-four triple path.
- All nine affected Goal 107 segment sources compiled in 54.46s:
  `192,201,232,242,278,290,325,336,364` (each `segment_` suffix is zero-padded).
- General theorem axiom footprint: `propext`, `Classical.choice`, `Quot.sound`.
  Generated graph certificates additionally use explicit `native_decide` axioms;
  no `sorryAx` or unexpected axiom was observed.
- GPT canonical bundle regenerated byte-identically: 97 files / 1,968,291 bytes.
  This checks the selected public targets only, not backward Goal 107.

These are focused research receipts, not a new full-suite/three-model publication.

## Remaining ordinary TP and other axes

Fixed-layout/fixed-rank BW_linear families, BW_layernorm parameter reductions,
and BW_multiref sum backends still require their own semantic migrations.
Then proceed to CP/ring, EP/MoE, DP, PP and only compose independently closed
axes. Arbitrary `DP×TP×PP×CP×EP` configuration support is not implemented.

YOCO's two-rank zigzag/ring rules are a separate CP/EP topology problem and are not evidence that ordinary TP remains limited to two ranks.
