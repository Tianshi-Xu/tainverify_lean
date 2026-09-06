import denote.Denote

/-! Row-level refinement of the pinned nnScaler front/end prefix algorithm.

For one equal-length sequence N = 2*K*d, the source uses Q halves of length d,
K prefixes (r+1)*d and (2*K-r)*d, and bottom-right causal alignment. This module
proves the resulting masks, normalization sums and weighted rows agree with
canonical global-position rows. It does not model GPU arithmetic, Q extraction,
GQA head assignment or the tensor-level gather/scatter wrapper.
-/

namespace TrainVerify.Denote.ZigzagAttentionSource

/-- The mathematical row used by Denote: masked slots are excluded from both
normalization and the weighted output, including its explicit zero-sum branch.
`weight j` is the exponential of the Q/K logit at logical key position j. -/
noncomputable def causalRow (length query : Nat) (weight value : Nat → Scalar) : Scalar :=
  let denom := ∑ j ∈ Finset.range length,
    if attnMaskedAt true 0 query j then 0 else weight j
  ∑ j ∈ Finset.range length,
    (if attnMaskedAt true 0 query j then 0
     else if denom = 0 then 0 else weight j / denom) * value j

/-- Bottom-right alignment adds the K-length minus Q-length to the local row. -/
noncomputable def branchRow (prefLen half idx : Nat) (weight value : Nat → Scalar) : Scalar :=
  causalRow prefLen (idx + (prefLen - half)) weight value

private theorem masked_iff (query key : Nat) :
    attnMaskedAt true 0 query key = decide (query < key) := by
  simp only [attnMaskedAt, Bool.true_and, Nat.lt_irrefl, decide_false,
    Bool.false_and, Bool.or_false]

/-- Extending a causal row past the query adds only masked zeros. -/
theorem causal_sum_prefix (prefLen total query : Nat) (weight : Nat → Scalar)
    (hprefLen : prefLen ≤ total) (hquery : query < prefLen) :
    (∑ j ∈ Finset.range prefLen,
      if attnMaskedAt true 0 query j then 0 else weight j) =
    ∑ j ∈ Finset.range total,
      if attnMaskedAt true 0 query j then 0 else weight j := by
  apply Finset.sum_subset (Finset.range_mono hprefLen)
  intro j _ hj
  have hj' : prefLen ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  have hmasked : attnMaskedAt true 0 query j = true := by
    rw [masked_iff]
    exact decide_eq_true (lt_of_lt_of_le hquery hj')
  rw [if_pos hmasked]

/-- Prefix/full attention equality holds for arbitrary logit weights and values;
there is no positivity or nonzero-denominator assumption hidden in the bridge. -/
theorem causal_row_prefix (prefLen total query : Nat) (weight value : Nat → Scalar)
    (hprefLen : prefLen ≤ total) (hquery : query < prefLen) :
    causalRow prefLen query weight value = causalRow total query weight value := by
  unfold causalRow
  rw [causal_sum_prefix prefLen total query weight hprefLen hquery]
  apply Finset.sum_subset (Finset.range_mono hprefLen)
  intro j _ hj
  have hj' : prefLen ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  have hmasked : attnMaskedAt true 0 query j = true := by
    rw [masked_iff]
    exact decide_eq_true (lt_of_lt_of_le hquery hj')
  rw [if_pos hmasked, zero_mul]

/-- General block: prefLen = offset + half, so bottom-right causal alignment
restores the logical Q offset before normalization. -/
theorem branch_row_eq (offset half total idx : Nat) (weight value : Nat → Scalar)
    (hidx : idx < half) (hprefLen : offset + half ≤ total) :
    branchRow (offset + half) half idx weight value =
      causalRow total (offset + idx) weight value := by
  unfold branchRow
  rw [Nat.add_sub_cancel, Nat.add_comm idx offset]
  exact causal_row_prefix (offset + half) total (offset + idx) weight value
    hprefLen (Nat.add_lt_add_left hidx offset)

/-- Source front prefix `(rank+1)*d` restores global row `rank*d + idx`. -/
theorem front_row_eq (K rank d idx : Nat) (weight value : Nat → Scalar)
    (hrank : rank < K) (hidx : idx < d) :
    branchRow ((rank + 1) * d) d idx weight value =
      causalRow (2 * K * d) (rank * d + idx) weight value := by
  have hprefLen : rank * d + d ≤ 2 * K * d := by
    calc
      rank * d + d = (rank + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (2 * K) * d := Nat.mul_le_mul_right d (by omega)
  rw [Nat.add_mul, Nat.one_mul]
  exact branch_row_eq (rank * d) d (2 * K * d) idx weight value hidx hprefLen

/-- Source end prefix `(2*K-rank)*d` restores row `(2*K-rank-1)*d + idx`. -/
theorem end_row_eq (K rank d idx : Nat) (weight value : Nat → Scalar)
    (hrank : rank < K) (hidx : idx < d) :
    branchRow ((2 * K - rank) * d) d idx weight value =
      causalRow (2 * K * d) ((2 * K - rank - 1) * d + idx) weight value := by
  have hsplit : (2 * K - rank - 1) * d + d = (2 * K - rank) * d := by
    calc
      _ = (2 * K - rank - 1 + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
      _ = _ := by congr 1; omega
  have hprefLen : (2 * K - rank - 1) * d + d ≤ 2 * K * d := by
    rw [hsplit]
    exact Nat.mul_le_mul_right d (Nat.sub_le _ _)
  rw [← hsplit]
  exact branch_row_eq ((2 * K - rank - 1) * d) d (2 * K * d) idx
    weight value hidx hprefLen

/-- Connect the row model to the actual single-sequence Denote tensor output.
The row/head/channel indices are exactly those decoded by `fw_attn_varlen`. -/
theorem fw_attn_varlen_row (q k v cu : Tensor) (N qh kvh d vd outIdx : Nat)
    (hq : q.shape.head? = some N) (hcu : decodeCuSeqlens cu = [0, N])
    (hbound : outIdx < prodShape [N, qh, vd]) (hrow : outIdx / vd / qh < N) :
    valAt (fw_attn_varlen q k v cu cu qh kvh d vd true 0) outIdx =
      causalRow N (outIdx / vd / qh)
        (fun j => expFn (attnDotQK q k qh kvh d (outIdx / vd / qh)
          (outIdx / vd % qh) j
          (if (if kvh = 0 then 1 else qh / kvh) = 0 then outIdx / vd % qh
           else (outIdx / vd % qh) / (if kvh = 0 then 1 else qh / kvh)) * attnScale d))
        (fun j => valAt v ((j * kvh +
          (if (if kvh = 0 then 1 else qh / kvh) = 0 then outIdx / vd % qh
           else (outIdx / vd % qh) / (if kvh = 0 then 1 else qh / kvh))) * vd + outIdx % vd)) := by
  have hb : outIdx < prodShape (fw_attn_varlen q k v cu cu qh kvh d vd true 0).shape := by
    change outIdx < prodShape [(q.shape.head?).getD 0, qh, vd]
    rw [hq]
    exact hbound
  rw [valAt_of_lt _ _ hb]
  have hseq : attnFindSeq [0, N] (outIdx / vd / qh) = 0 := by
    simp only [attnFindSeq, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, attnFindSeqAux, List.getD_cons_succ, List.getD_cons_zero,
      if_pos hrow]
  dsimp only [fw_attn_varlen, Tensor.mkShape]
  simp only [hcu, hseq, List.getD_cons_zero, List.getD_cons_succ,
    Nat.zero_add, Nat.sub_zero, causalRow]

end TrainVerify.Denote.ZigzagAttentionSource
