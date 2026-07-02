# Pattern_1 Assembly Plan

## Overview
- **Goal**: `goal_1 = { ts := 4673, tsShape := [4096], tps := [{rank:=0, tid:=4673}] }` — singleton reconstruct
- **SM**: 25 nodes computing final loss `[4096]`
- **PM**: 53 nodes (2 chunk + 50 op + 1 allGather) also producing `[4096]`
- Both computations equal by dim-0 sharding invariance.

## Boundary tids (13 total in sm_goal_1InitShapes)

**Sharded (3)** — from intermediateGoals:
- 5893 [4096, 1024] → allGather_0 [initPM 11609, initPM 11610] shape [2048, 1024]
- 5895 [4096, 1024] → allGather_0 [initPM 11613, initPM 11614] shape [2048, 1024]
- 5898 [4096, 64]   → allGather_0 [initPM 11621, initPM 11622] shape [2048, 64]

**Identity (10)** — same tid in both init envs:
- 4678 [4096] (labels — chunked by PM at boundary via ChunkPrim)
- 5902 [64, 1024, 1024], 5903 [64, 1024, 512] (moe_gmm weights)
- 5906 [1, 1024], 5911 [512, 1024], 5915 [512, 1024], 5920 [1024, 512] (linear weights)
- 5927 [2] (unshuffle param)
- 5929 [1024] (rms_norm scale)
- 5931 [154880, 1024] (embedding weight for inner_chunk_ce)

## SM computation flow (with expected shapes)

| SM# | Op | Ins (shape) | Outs (shape) | Notes |
|---|---|---|---|---|
| 0 | fw_multiref | 5893 [4096,1024] | 8576, 8580 [4096,1024]×2 | id 2-way |
| 1 | fw_multiref | 5895 [4096,1024] | 8587,8591,8595,8599,8603 [4096,1024]×5 | id 5-way |
| 2 | fw_reshape | 8595 | 5905 | reshape [4096,1024] → ? |
| 3 | fw_reshape | 8599 | 5910 | |
| 4 | fw_reshape | 8603 | 5914 | |
| 5 | fw_mix_precision_linear | 5905, 5906 [1,1024] | 5907 | linear |
| 6 | fw_mix_precision_linear | 5910, 5911 [512,1024] | 5912 | linear |
| 7 | fw_mix_precision_linear | 5914, 5915 [512,1024] | 5916 | linear |
| 8 | fw_topk_routing | 5898 [4096,64] | 5899,5900,5901 [4096, ?] | topk (from Pattern_4) |
| 9 | fw_view | 5907 | 5908 [4096,1] | view |
| 10 | fw_view | 5912 | 5913 [4096,512] | view |
| 11 | fw_view | 5916 | 5917 [4096,512] | view |
| 12 | fw_all2all_moe_gmm | 8591, 5899, 5900, 5902, 5903 | 5904 | MoE gemm |
| 13 | fw_sigmoid | 5908 | 5909 | element-wise |
| 14 | fw_swiglu | 5913, 5917 | 5918 | element-wise fused |
| 15 | fw_reshape | 5918 | 5919 | |
| 16 | fw_mix_precision_linear | 5919, 5920 [1024,512] | 5921 | linear |
| 17 | fw_view | 5921 | 5922 [4096,1024] | view |
| 18 | fw_mul | 5909, 5922 | 5923 | element-wise |
| 19 | fw_add | 5904, 5923 | 5924 | element-wise |
| 20 | fw_float | 5924 | 5925 | cast |
| 21 | fw_add | 8580, 5925 | 5926 [4096,1024] | element-wise |
| 22 | fw_maybe_unshuffle | 5926, 5927 [2] | 5928 | reorder shards |
| 23 | fw_rms_norm | 5928, 5929 [1024] | 5930 | row-wise |
| 24 | fw_inner_chunk_ce | 5930, 5931 [154880,1024], 4678 [4096] | 4673, 4674 [4096]×2 | reduction |

## Required commute lemmas (~14 op families)

### Trivially element-wise (5)
- `fw_add`, `fw_mul`, `fw_sigmoid`, `fw_swiglu`, `fw_float`: `f (allGather [a, b]) = allGather [f a, f b]` (for element-wise f)

### Row-wise (need dim-0 sharding respect) (3)
- `fw_softmax` (have via Pattern_4)
- `fw_rms_norm`: reduction on last dim
- `fw_inner_chunk_ce`: row-wise per-token

### Shape-manipulation (3)
- `fw_reshape`: preserves values, needs sharded dim mapping
- `fw_view`: same
- `fw_multiref`: identity/replication

### Non-trivial (3)
- `fw_mix_precision_linear`: `linear(x, W) = x @ W.T` where x is sharded on batch dim
- `fw_topk_routing` (have via Pattern_4)
- `fw_all2all_moe_gmm`: expert-parallel
- `fw_maybe_unshuffle`: shard rearrangement

### Boundary
- allGather_0 ↔ chunk round-trip (for 4678 → chunk_0/chunk_1)

## Assembly strategy

Given all ops commute with dim-0 sharding, the proof structure:

```
smStore 4673 = pmStore 4673 = allGather_0 [pmStore 11837, pmStore 11838]
```

By boundary + per-op commute, prove for each intermediate SM tid X:
```
smStore X = allGather_0 [pmStore X_r0, pmStore X_r1]
```

by induction on SM node order. Each induction step uses the specific op's commute lemma.

## Estimated effort

- **applyNode_fw_XXX_out helpers**: ~10 new ones needed (add, mul, sigmoid, swiglu, float, reshape, view, mix_precision_linear, rms_norm, maybe_unshuffle, multiref_2/multiref_5, all2all_moe_gmm, inner_chunk_ce) — ~600 LOC
- **Sharding commute lemmas**: ~14 lemmas, each ~50-150 LOC — ~1500 LOC
- **SM machinery denote_sm_goal_1_4673**: 25 sequential rewrites — ~200 LOC
- **PM machinery denote_pm_goal_1_4673**: 53 sequential rewrites — ~500 LOC
- **Boundary/intermediate extractions**: 3 sharded + 10 identity — ~150 LOC (helpers reusable from Pattern_4)
- **Value assembly**: chain 25 commute steps to prove sm 4673 = pm 4673 — ~300 LOC

**Total: ~3200 LOC realistic**, ~6-10h focused work.

## Risks

1. **all2all_moe_gmm** semantics: this involves cross-rank communication. The commute law may not be a pure dim-0 sharding — it's expert-parallel with expert allocation.
2. **maybe_unshuffle** params `[1, 0]` (SM) vs `[2, 0], [2, 1]` (PM): SM uses "unshuffle 1-way rank 0" (no-op?), PM uses "unshuffle 2-way rank r". Semantics needs careful check.
3. **mix_precision_linear** sharding: PM linear takes chunk of input × full weight. If output = x @ W.T, sharding x on rows gives sharded output rows.

## Order of attack

1. **Setup**: check all `applyNode_XXX_out` helpers, add missing ones.
2. **Element-wise commute lemmas** (easiest, ~5 lemmas).
3. **Row-wise commute lemmas** (rms_norm, inner_chunk_ce).
4. **Shape/reshape commute lemmas**.
5. **mix_precision_linear commute** (batch sharding).
6. **maybe_unshuffle**: check semantics carefully.
7. **all2all_moe_gmm**: potentially blocked, may need axiom.
8. **SM machinery**: assemble denote_sm_goal_1_4673.
9. **PM machinery**: assemble denote_pm_goal_1_4673.
10. **Value assembly**: chain via boundary + per-op commute.
