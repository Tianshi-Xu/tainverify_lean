# Transpose Batch: Chunk-based Cut Goals

## Summary
**26/26 goals proven, 0 blocked.**

## Goals Proven

### FW_transpose (13 goals)
| Goal | Input Shape | Chunk Dim | Bridge Lemma |
|------|-------------|-----------|--------------|
| 10   | [1,8,4,8]  | 3         | fw_transpose12_split_dim3_4_1_8_4_8 |
| 14   | [1,8,4,8]  | 3         | fw_transpose12_split_dim3_4_1_8_4_8 |
| 35   | [1,8,4,8]  | 3         | fw_transpose12_split_dim3_4_1_8_4_8 |
| 60   | [1,8,4,8]  | 3         | fw_transpose12_split_dim3_4_1_8_4_8 |
| 85   | [1,8,4,8]  | 3         | fw_transpose12_split_dim3_4_1_8_4_8 |
| 12   | [1,8,4,8]  | 1         | fw_transpose12_split_dim1_4_1_8_4_8 |
| 37   | [1,8,4,8]  | 1         | fw_transpose12_split_dim1_4_1_8_4_8 |
| 62   | [1,8,4,8]  | 1         | fw_transpose12_split_dim1_4_1_8_4_8 |
| 87   | [1,8,4,8]  | 1         | fw_transpose12_split_dim1_4_1_8_4_8 |
| 39   | [1,8,4,8]  | 2         | fw_transpose12_split_dim2_4_1_8_4_8 |
| 64   | [1,8,4,8]  | 2         | fw_transpose12_split_dim2_4_1_8_4_8 |
| 89   | [1,8,4,8]  | 2         | fw_transpose12_split_dim2_4_1_8_4_8 |
| 45   | [1,4,8,8]  | 3         | fw_transpose12_split_dim3_4_1_4_8_8 |

### BW_transpose (13 goals)
| Goal | Grad Shape  | PM AllGather Dim | Bridge Lemma |
|------|-------------|------------------|--------------|
| 121  | [1,4,8,8]  | 3                | bw_transpose12_gather3_4_1_4_8_2 |
| 125  | [1,4,8,8]  | 3                | bw_transpose12_gather3_4_1_4_8_2 |
| 160  | [1,4,8,8]  | 3                | bw_transpose12_gather3_4_1_4_8_2 |
| 193  | [1,4,8,8]  | 3                | bw_transpose12_gather3_4_1_4_8_2 |
| 228  | [1,4,8,8]  | 3                | bw_transpose12_gather3_4_1_4_8_2 |
| 123  | [1,4,8,8]  | 2                | bw_transpose12_gather1_to_2_4_1_1_8_8 |
| 158  | [1,4,8,8]  | 2                | bw_transpose12_gather1_to_2_4_1_1_8_8 |
| 191  | [1,4,8,8]  | 2                | bw_transpose12_gather1_to_2_4_1_1_8_8 |
| 226  | [1,4,8,8]  | 2                | bw_transpose12_gather1_to_2_4_1_1_8_8 |
| 156  | [1,4,8,8]  | 1                | bw_transpose12_gather2_to_1_4_1_4_2_8 |
| 195  | [1,4,8,8]  | 1                | bw_transpose12_gather2_to_1_4_1_4_2_8 |
| 230  | [1,4,8,8]  | 1                | bw_transpose12_gather2_to_1_4_1_4_2_8 |
| 166  | [1,8,4,8]  | 3                | bw_transpose12_gather3_4_1_8_4_2 |

## Bridge Lemmas Added (in Denote.lean)

### FW Bridge Lemmas
- `fw_transpose12_split_dim3_4_1_8_4_8`: transposeAxes 1 2 commutes with chunk/gather on dim 3, shape [1,8,4,8]
- `fw_transpose12_split_dim1_4_1_8_4_8`: same, chunk on dim 1
- `fw_transpose12_split_dim2_4_1_8_4_8`: same, chunk on dim 2
- `fw_transpose12_split_dim3_4_1_4_8_8`: transposeAxes 1 2 on [1,4,8,8], chunk dim 3

### BW Bridge Lemmas
- `bw_transpose12_gather3_4_1_4_8_2`: BW transpose with shards [1,4,8,2], gather dim 3
- `bw_transpose12_gather1_to_2_4_1_1_8_8`: BW transpose with shards [1,1,8,8], gather dim→2
- `bw_transpose12_gather2_to_1_4_1_4_2_8`: BW transpose with shards [1,4,2,8], gather dim→1
- `bw_transpose12_gather3_4_1_8_4_2`: BW transpose with shards [1,8,4,2], gather dim 3

### Supporting Infrastructure
- `applyNode_bw_transposeAxes_out`: applyNode theorem for BW_transpose
- `applyNode_allGatherPrimDimN_out_thm`: applyNode theorem for AllGatherPrim
- Various `valAt` helper lemmas for index arithmetic

## Axioms
All 26 proofs depend only on: `propext`, `Classical.choice`, `Quot.sound` (+ baseline scalar axioms: erfFn, expFn, piScalar, sqrtFn, scalarToNat).

## Blocked Goals
None.
