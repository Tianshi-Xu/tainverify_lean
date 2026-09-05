import denote.Denote

namespace TrainVerify.Denote

noncomputable section

/-- Pointwise rank-3 characterization of a dim-2 gather. -/
private theorem allGatherPrimDimN_2_valAt_rank3
    (xs : List Tensor) (K d0 d1 d2 idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0, d1, d2])
    (hK : K ≠ 0) (hd2 : d2 ≠ 0)
    (hidx : idx < d0 * d1 * (d2 * K)) :
    valAt (allGatherPrimDimN 2 K 0 xs) idx =
      valAt
        (xs.getD ((idx % (d2 * K)) / d2) (zeroTensor [d0, d1, d2]))
        (idx / (d2 * K) * d2 + idx % (d2 * K) % d2) := by
  have hs : (allGatherPrimDimN 2 K 0 xs).shape = [d0, d1, d2 * K] := by
    rw [allGatherPrimDimN_shape 2 K xs [d0, d1, d2] hhead]
    simp [List.set, List.getD]
  rw [valAt_of_lt _ _ (by
    rw [hs]
    simpa [prodShape, Nat.mul_assoc] using hidx)]
  have hmul : d2 * K ≠ 0 := Nat.mul_ne_zero hd2 hK
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.drop, List.foldl,
    Nat.reduceAdd, Nat.one_mul, Nat.mul_one, Nat.div_one, Nat.mod_one,
    Nat.add_zero, hmul, hd2, Nat.one_ne_zero, if_false]

/-- Scalar `BW_sum` commutes with an arbitrary nonempty ordered dim-2 gather
of homogeneous positive-width rank-3 shards. The rank count is exactly
`xs.length`; no power-of-two or fixed-size assumption is used. -/
theorem bw_sum_allGatherPrimDimN_dim2_rank3
    (g : Tensor) (xs : List Tensor) (d0 d1 d2 : Nat)
    (hne : xs ≠ []) (hd2 : 0 < d2)
    (hshapes : ∀ x ∈ xs, x.shape = [d0, d1, d2]) :
    bw_sum g (allGatherPrimDimN 2 xs.length 0 xs) =
      allGatherPrimDimN 2 xs.length 0 (xs.map (bw_sum g)) := by
  have hK : 0 < xs.length := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons _ _ => simp
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0, d1, d2] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  have hmaphead : ((xs.map (bw_sum g)).head?.map (fun t => t.shape)).getD [] =
      [d0, d1, d2] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simp [bw_sum_shape, hshapes x (by simp)]
  have hgather_shape : (allGatherPrimDimN 2 xs.length 0 xs).shape =
      [d0, d1, d2 * xs.length] := by
    rw [allGatherPrimDimN_shape 2 xs.length _ [d0, d1, d2] hhead]
    simp [List.set, List.getD]
  have hlhs_shape : (bw_sum g (allGatherPrimDimN 2 xs.length 0 xs)).shape =
      [d0, d1, d2 * xs.length] := by
    rw [bw_sum_shape, hgather_shape]
  have hrhs_shape : (allGatherPrimDimN 2 xs.length 0 (xs.map (bw_sum g))).shape =
      [d0, d1, d2 * xs.length] := by
    rw [allGatherPrimDimN_shape 2 xs.length _ [d0, d1, d2] hmaphead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx_bound : idx < d0 * d1 * (d2 * xs.length) := by
    have := hidx
    rw [hlhs_shape] at this
    simpa [prodShape, Nat.mul_assoc] using this
  conv_lhs =>
    rw [bw_sum_valAt_of_lt g _ idx (by
      rw [hgather_shape]
      simpa [prodShape, Nat.mul_assoc] using hidx_bound)]
  rw [allGatherPrimDimN_2_valAt_rank3
    (xs.map (bw_sum g)) xs.length d0 d1 d2 idx hmaphead
    (Nat.ne_of_gt hK) (Nat.ne_of_gt hd2) hidx_bound]
  have hfull_pos : 0 < d2 * xs.length := Nat.mul_pos hd2 hK
  have hrank_lt : idx % (d2 * xs.length) / d2 < xs.length := by
    rw [Nat.div_lt_iff_lt_mul hd2]
    simpa [Nat.mul_comm] using Nat.mod_lt idx hfull_pos
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hrank_lt, Option.map_some, Option.getD_some]
  have hpre_lt : idx / (d2 * xs.length) < d0 * d1 := by
    rw [Nat.div_lt_iff_lt_mul hfull_pos]
    simpa [Nat.mul_assoc] using hidx_bound
  have hlocal_lt : idx / (d2 * xs.length) * d2 + idx % (d2 * xs.length) % d2 <
      d0 * d1 * d2 := by
    have hrem_lt := Nat.mod_lt (idx % (d2 * xs.length)) hd2
    have hstep : idx / (d2 * xs.length) * d2 + idx % (d2 * xs.length) % d2 <
        (idx / (d2 * xs.length) + 1) * d2 := by
      rw [Nat.add_mul]
      omega
    exact lt_of_lt_of_le hstep
      (Nat.mul_le_mul_right d2 (Nat.succ_le_of_lt hpre_lt))
  exact (bw_sum_valAt_of_lt g _ _ (by
    rw [hshapes xs[idx % (d2 * xs.length) / d2] (List.getElem_mem _)]
    simpa [prodShape, Nat.mul_assoc] using hlocal_lt)).symm

end

end TrainVerify.Denote
