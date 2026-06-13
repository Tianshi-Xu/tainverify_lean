# BW_layernorm CROSS_DP Weight/Bias Gradient Batch Report

## Summary
**18/18 goals proven, 0 blocked.**

## Goals Proven

| Goal | Type | Target Tid | Status |
|------|------|-----------|--------|
| 112 | dw | 725 | ✅ proven |
| 113 | db | 726 | ✅ proven |
| 138 | dw | 756 | ✅ proven |
| 139 | db | 757 | ✅ proven |
| 147 | dw | 767 | ✅ proven |
| 148 | db | 768 | ✅ proven |
| 173 | dw | 798 | ✅ proven |
| 174 | db | 799 | ✅ proven |
| 182 | dw | 809 | ✅ proven |
| 183 | db | 810 | ✅ proven |
| 208 | dw | 840 | ✅ proven |
| 209 | db | 841 | ✅ proven |
| 217 | dw | 851 | ✅ proven |
| 218 | db | 852 | ✅ proven |
| 243 | dw | 882 | ✅ proven |
| 244 | db | 883 | ✅ proven |
| 252 | dw | 891 | ✅ proven |
| 253 | db | 892 | ✅ proven |

## Lemmas Added to Denote.lean

1. `evalOp_cross_dp_wred` — unfolds evalOp for CROSS_DP_WRED
2. `applyNode_cross_dp_wred_out` — singleton-output applyNode for CROSS_DP_WRED
3. `evalOp_bw_layernorm` — unfolds evalOp for BW_layernorm to (dx, dw, db)
4. `applyNode_bw_layernorm_dw_out` — extracts dw (index 1) from BW_layernorm node
5. `applyNode_bw_layernorm_db_out` — extracts db (index 2) from BW_layernorm node
6. `bw_layernorm_dw_eq` — unfolds dw formula with explicit sum over rows
7. `bw_layernorm_db_eq` — unfolds db formula with explicit sum over rows
8. `bw_layernorm_dw_shape` — shape of dw output = w.shape
9. `bw_layernorm_db_shape` — shape of db output = b.shape
10. `layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32` — mean on gather = mean on shard
11. `layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32` — var on gather = var on shard
12. `bw_layernorm_dw_dp_split_dim1_4_1_2_32` — **core lemma**: dw on gathered = tensorSum of per-shard dw
13. `bw_layernorm_db_dp_split_dim1_4_1_2_32` — **core lemma**: db on gathered = tensorSum of per-shard db

## Proof Strategy

The core insight: `bw_layernorm` computes dw[j] = Σ_row f(row,j) where f depends on
per-row statistics (mean, var). Since layernorm normalizes along the last dimension (d=32),
these per-row statistics are identical whether computed on the full tensor or any row-block shard.
The 4 DP ranks each process a contiguous row-block (2 rows each from 8 total), established
by the dim-1 allGather prereqs. The sum over all 8 rows decomposes into 4 sums of 2 rows each,
matching tensorSum of the 4 per-rank dw outputs.

## Axioms Used
Only allowed axioms: propext, Classical.choice, Quot.sound + baseline scalar axioms
(erfFn, expFn, piScalar, scalarToNat, sqrtFn).
