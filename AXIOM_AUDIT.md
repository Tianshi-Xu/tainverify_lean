# Pattern_1 Axiom Truth Audit — 2026-07-03

**Goal**: Verify each axiom is mathematically true (not just conveniently assumed).
If false → Pattern_1's proof is invalid; must redo.

## Method
For each `axiom X_allGather0_commute_2`, determine:
- **What is the function's definition?**
- **Is the value at each index preserved after sharding→gather?**
- **Verdict**: TRUE / FALSE / CONDITIONAL

---

## 1. `fw_add_allGather0_commute_2`

**Def**: `elemwiseAdd x y = mkShape (outShape2 x y) (fun i => broadcastValAtShape ... x + broadcastValAtShape ... y)`

**Statement**:
```
elemwiseAdd (allGather [a, b]) (allGather [c, d])
  = allGather [elemwiseAdd a c, elemwiseAdd b d]
```

**Analysis**: When shapes match (a,c same shape; b,d same shape; a,c and b,d compatible after gather):
- `outShape2 (allGather [a,b]) (allGather [c,d])` = shape of gather (since same length)
- LHS at [l, e] = gather_ab[l,e] + gather_cd[l,e] = (rank r's a-shard[l',e]) + (rank r's c-shard[l',e])
- RHS at [l, e]: allGather [add_ac, add_bd][l,e] = (rank r's add_(a,c)[l',e] or add_(b,d)[l',e])
- Both are same value.

**Verdict**: ✅ **TRUE when all 4 tensors have same-shape shards.**
**Pattern_1 usage**: Sometimes shapes mismatch (broadcast). In those cases the axiom needs generalization.

---

## 2. `fw_mul_allGather0_commute_2`

Same structure as add. **Verdict**: ✅ **TRUE for same-shape case, needs care for broadcast.**

---

## 3. `fw_sigmoid_allGather0_commute_2` ✅ PROVEN

Row/element-local. Provably true.

---

## 4. `fw_swiglu_allGather0_commute_2` ✅ PROVEN

Element-local (per (gate, up) pair). Provably true.

---

## 5. `fw_rms_norm_allGather0_commute_2` ✅ PROVEN (2-dim version)

Row-local reduction. Provably true.
`_axiom` variant is for 1-dim shard case (also true, just needs separate proof).

---

## 6. `fw_linear_allGather0_commute_2`

**Def**: fw_linear x w = ... (matmul)

**Statement**:
```
fw_linear (allGather [a, b]) w
  = allGather [fw_linear a w, fw_linear b w]
```

**Analysis**: 
- Linear layer: `y[l, out_c] = Σ_in_c x[l, in_c] * w[in_c, out_c]` (or transpose)
- Row l depends only on row l of x (not on other rows)
- allGather on dim 0 preserves rows; linear on gathered = concat of per-rank linear.

**Verdict**: ✅ **TRUE (row-local matmul).**

---

## 7. `fw_view_allGather0_commute_2`

**Def**: fw_view targetShape x = mkShape targetShape (fun i => valAt x i.1) — reshape, same flat data.

**Statement**:
```
fw_view sh_full (allGather [a, b])
  = allGather [fw_view sh_shard a, fw_view sh_shard b]
```

**Analysis**:
- View reshapes without moving data. valAt (view sh x) i = valAt x i (raw index).
- allGather concatenates on dim 0.
- If we view the concatenated tensor with sh_full = [d*2, rest], each "chunk" of the reshape is a per-rank shard viewed with [d, rest].

**Verdict**: ✅ **TRUE if sh_full has first dim = 2 × (sh_shard first dim) and other dims match.**
Requires the shape compatibility condition (currently unstated in axiom).

---

## 8. `fw_topk_routing_fst_allGather0_commute_2` ✅ VERIFIED TRUE

Softmax + topk_rank + inTopK + topkScoreSum + topkScoresAt all row-local (per input row l).
For sharding on dim 0, rows split cleanly. Provable via same technique as Pattern_4's Lemma A.

---

## 9. `fw_topk_routing_snd_fst_allGather0_commute_2`

Same as above — routing_map is [l, e] entry indicator, computed via `inTopK gate_scores l e`.
Row-local. **Verdict**: ✅ **TRUE.**

---

## 10. `fw_all2all_moe_gmm_split_commute_2`

**Def**: fw_all2all_moe_gmm involves expert-parallel computation, permute, gemm, unpermute.

**Statement**:
```
fw_all2all_moe_gmm (allGather [input_a, input_b])
                   (allGather [rp_a, rp_b])
                   (allGather [rm_a, rm_b])
                   (allGather [w13_a, w13_b])  -- expert-sharded weights [64 experts → 32/rank]
                   (allGather [w2_a, w2_b])
                   64 0 64 topK swigluLimit
  = allGather [fw_all2all_moe_gmm input_a rp_a rm_a w13_a w2_a 64 0 32 ...,   -- rank 0: experts [0, 32)
               fw_all2all_moe_gmm input_b rp_b rm_b w13_b w2_b 64 32 64 ...]  -- rank 1: experts [32, 64)
```

**Analysis**: 
- This is **expert-parallel split**: rank r handles experts [r*32, (r+1)*32).
- MoE math: `out[l] = Σ_e routing_probs[l, e] · down_e(swiglu(gate_e(x[l]), up_e(x[l])))`
- If routing_probs[l, e] is nonzero only for e ∈ rank_r's expert range for rank_r's tokens, then splitting works.
- **CRITICAL**: This depends on the exact `routing_probs` and `routing_map` values matching the expert partition.
- Also depends on whether the graph feeds `input = allGather [x_a, x_b]` (tokens sharded) with **matched** routing that goes to the right expert on the right rank.

**Verdict**: ⚠️ **CONDITIONALLY TRUE, needs specific setup**. The exact semantics of `fw_all2all_moe_gmm` in Denote.lean must be checked — if it iterates over all experts and sums via routing_probs (regardless of shard), then per-rank shard only touches a subset of tokens (batch dim) not experts. In that case, expert-split doesn't quite work.

**Need to inspect Denote's fw_all2all_moe_gmm def to verify.**

---

## 11. `fw_maybe_unshuffle_cp2_commute`

**Def**: 
```
fw_maybe_unshuffle cu cpSize cpRank xs = 
  mkShape firstShape (fun outIdx =>
    let i = outIdx / hiddenStride, h = outIdx % hiddenStride
    let g = cpRank * chunkSize + i
    let srcRank = destRank cuList cpSize g
    let src = xs.getD srcRank
    valAt src (srcOffset * hiddenStride + h))
```

**Statement**:
```
fw_maybe_unshuffle (allGather [a, b]) 1 0 [cu]
  = allGather [fw_maybe_unshuffle a 2 0 [cu], fw_maybe_unshuffle b 2 1 [cu]]
```

**Analysis**:
- **`cpSize=1, cpRank=0`** on the LHS: this is essentially a no-op (or trivial) since cpSize=1 means "no context parallelism"
- **`cpSize=2`** on the RHS: full context parallel with 2 ranks
- LHS: unshuffle with cpSize=1 means each token maps to itself (destRank = 0 for all g since cpSize=1).
- RHS: per-rank cpSize=2 unshuffle — actually redistributes across ranks (zigzag).

**These are fundamentally different operations**:
- LHS = identity permutation on gather [a, b]
- RHS = distributed zigzag unshuffle where rank r pulls from computed srcRank

**Verdict**: ❌ **PROBABLY FALSE.** The two operations don't do the same thing.

**BUT**: In Pattern_1's usage, since `xs = [cu]` (metadata list, not data list), the axiom's actual semantics under Denote's cu-first binding is different. Both LHS and RHS operate on `xs.head?.shape = cu.shape = [2]`, so both produce shape [2] outputs. The values might coincidentally match because both use `cu` as data.

Let me trace:
- LHS: `fw_maybe_unshuffle (allGather [a, b]) 1 0 [cu]`
  - firstShape = cu.shape = [2]
  - For outIdx in [0, 2): i = outIdx, h = 0 (hiddenStride = 1)
  - g = 0 * 2 + i = i (cpRank=0, chunkSize=2)
  - srcRank = destRank cuList 1 g = 0 (cpSize=1)
  - src = [cu].getD 0 = cu
  - srcOffset = zigzagInvOffset cuList 1 0 g = ?
  - Output at i = valAt cu (srcOffset * 1 + 0) = valAt cu srcOffset

- RHS: `allGather [fw_maybe_unshuffle a 2 0 [cu], fw_maybe_unshuffle b 2 1 [cu]]`
  - Each per-rank has similar structure but with cpSize=2, cpRank=0 or 1
  - Also outputs shape [2] each (since firstShape = cu.shape = [2])
  - allGather on dim 0: shape [4]

**But LHS output shape = [2], RHS output shape = [4]. Shape mismatch!**

**Verdict**: ❌ **FALSE (shape mismatch)**.

This is a critical finding.

---

## 12. `fw_inner_chunk_ce_fst_allGather0_commute_2`

**Def**: `fw_inner_chunk_ce x w y vocab zLossScale = (losses, z_losses)` where each is [l] shape.

**Statement**:
```
(fw_inner_chunk_ce (allGather [x_a, x_b]) w y vocab zLossScale).fst
  = allGather [(fw_inner_chunk_ce x_a w (chunk_0 y) vocab zLossScale).fst,
               (fw_inner_chunk_ce x_b w (chunk_1 y) vocab zLossScale).fst]
```

**Analysis**: Cross-entropy loss per token: `losses[l] = -log(softmax(logits[l])[y[l]])`.
- Row-local computation.
- Label `y` also sharded on dim 0 (chunk_0, chunk_1).
- Each rank computes losses for its own tokens with its own labels.
- allGather concatenates the per-rank loss vectors.

**Verdict**: ✅ **TRUE** (row-local, label sharded correctly).

---

## 13. `sm_chain_shape_4096` & 14. `pm_chain_shape_4096`

**Statement**: `(denoteGraph sm_goal_1 initSM 4673).shape = [4096]`.

**Analysis**: 
- This is a **concrete shape claim about the specific graph output**.
- It's true if all the shape witnesses hold and all the ops produce the expected shapes.
- **Given the fw_maybe_unshuffle shape mismatch (output [2] not [4096, 1024])**, the final shape of `sm_goal_1` might NOT be [4096].
- Under Denote's literal semantics, output of fw_inner_chunk_ce.fst = [(x.shape.head?).getD 0]. If x has shape [2] (from unshuffle), then output = [2], not [4096].

**Verdict**: ⚠️ **PROBABLY FALSE under Denote's literal semantics**, but the graph's intermediate shapes claim it should be [4096]. **Discrepancy!**

---

# SUMMARY

## Definitely True (should prove):
1. fw_add (same-shape) ✅
2. fw_mul (same-shape) ✅
3. fw_sigmoid ✅ PROVEN
4. fw_swiglu ✅ PROVEN
5. fw_rms_norm ✅ PROVEN (2-dim)
6. fw_linear ✅
7. fw_view (with compat) ✅
8. fw_topk_routing_fst ✅ (row-local)
9. fw_topk_routing_snd_fst ✅
12. fw_inner_chunk_ce_fst ✅

## Conditionally True (need setup verification):
10. fw_all2all_moe_gmm_split — needs Denote def inspection
2/1. fw_add/mul with broadcasting — needs handling mismatched shapes

## PROBABLY FALSE / CRITICAL:
11. **fw_maybe_unshuffle_cp2_commute** — shape mismatch (LHS [2], RHS [4])
13-14. **sm/pm_chain_shape_4096** — probably false given #11

## Next Actions
1. **Verify fw_maybe_unshuffle_cp2_commute** by writing a test that concretely evaluates both sides
2. If false: **Pattern_1's proof is unsound** — need to rework
3. Determine what the actual correct sharding-commute is for the "graph-intended" semantics
