import denote.KRankLinearGather

namespace TrainVerify.Denote
noncomputable section

/-- dX's feature width may vary with the ordered tensor-parallel group. -/
theorem bw_linear_fst_valAt_1_8
    (g x w : Tensor) (o i : Nat)
    (hg : g.shape = [1, 8, o]) (hx : x.shape = [1, 8, i]) (hw : w.shape = [o, i])
    (P : Nat) (hP : P < 8) (col : Nat) (hcol : col < i) :
    valAt (bw_linear g x w).1 (P * i + col) =
      ∑ j ∈ Finset.range o, valAt g (P * o + j) * valAt w (j * i + col) := by
  have hi : 0 < i := by omega
  have hidx : P * i + col < 8 * i := by
    calc
      _ < P * i + i := Nat.add_lt_add_left hcol _
      _ = (P + 1) * i := by ring
      _ ≤ 8 * i := Nat.mul_le_mul_right i hP
  unfold bw_linear
  simp only [hg, hx, hw]
  rw [valAt_of_lt _ _ (by simpa [Tensor.mkShape, prodShape] using hidx)]
  simp only [Tensor.mkShape]
  have h8i : 0 < 8 * i := by omega
  have hdiv : (P * i + col) / i = P := by
    rw [show P * i + col = col + i * P by ring,
      Nat.add_mul_div_left _ _ hi, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmod : (P * i + col) % i = col := by
    rw [show P * i + col = col + i * P by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  simp only [if_neg hi.ne', if_neg h8i.ne', Nat.div_eq_of_lt hidx,
    Nat.mod_eq_of_lt hidx, hdiv, hmod, Nat.zero_mul, Nat.zero_add]

/-- Ordered weight-column shards reconstruct dX without reducing across ranks.
The local gradient, activation and weight shapes retain the checked positive-width ABI. -/
theorem bw_linear_dx_weight_allGatherPrimDimN_dim1_rank3
    (g x : Tensor) (xs ws : List Tensor) (o d : Nat)
    (ho : 0 < o) (hd : 0 < d)
    (hne : xs ≠ []) (hlen : ws.length = xs.length)
    (hg : g.shape = [1, 8, o]) (hx : x.shape = [1, 8, d * xs.length])
    (hxs : ∀ t ∈ xs, t.shape = [1, 8, d])
    (hws : ∀ t ∈ ws, t.shape = [o, d]) :
    (bw_linear g x (allGatherPrimDimN 1 ws.length 0 ws)).1 =
      allGatherPrimDimN 2 xs.length 0
        (List.zipWith (fun a w => (bw_linear g a w).1) xs ws) := by
  have hK : 0 < xs.length := List.length_pos_iff.mpr hne
  have hW : 0 < ws.length := by omega
  have hheadw : (ws.head?.map (fun t => t.shape)).getD [] = [o, d] := by
    cases ws with
    | nil => simp at hW
    | cons w rest => simpa using hws w (by simp)
  have hwsget (r : Nat) (hr : r < ws.length) :
      (ws.getD r (zeroTensor [o, d])).shape = [o, d] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
    exact hws ws[r] (List.getElem_mem _)
  have hxsget (r : Nat) (hr : r < xs.length) :
      (xs.getD r (zeroTensor [1, 8, d])).shape = [1, 8, d] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
    exact hxs xs[r] (List.getElem_mem _)
  have hWshape : (allGatherPrimDimN 1 ws.length 0 ws).shape = [o, d * xs.length] := by
    rw [allGatherPrimDimN_shape 1 ws.length ws [o, d] hheadw]
    simp [List.set, List.getD, hlen]
  have hLshape : (bw_linear g x (allGatherPrimDimN 1 ws.length 0 ws)).1.shape =
      [1, 8, d * xs.length] :=
    bw_linear_3d_fst_shape 1 8 o (d * xs.length) _ _ _ hg hx hWshape
  let pieces := List.zipWith (fun a w => (bw_linear g a w).1) xs ws
  have hplen : pieces.length = xs.length := by simp [pieces, List.length_zipWith, hlen]
  have hpget (r : Nat) (hr : r < xs.length) :
      pieces.getD r (zeroTensor [1, 8, d]) =
        (bw_linear g (xs.getD r (zeroTensor [1, 8, d]))
          (ws.getD r (zeroTensor [o, d]))).1 := by
    have hwr : r < ws.length := by omega
    have hpr : r < pieces.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpr]
    simp [pieces, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr,
      List.getElem?_eq_getElem hwr]
  have hpiecehead : (pieces.head?.map (fun t => t.shape)).getD [] = [1, 8, d] := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons a rest =>
      cases ws with
      | nil => simp at hlen
      | cons w wrest =>
        simp [pieces, bw_linear_3d_fst_shape 1 8 o d g a w hg
          (hxs a (by simp)) (hws w (by simp))]
  have hRshape : (allGatherPrimDimN 2 xs.length 0 pieces).shape = [1, 8, d * xs.length] := by
    rw [allGatherPrimDimN_shape 2 xs.length pieces [1, 8, d] hpiecehead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLshape, hRshape])
  intro idx hidx
  rw [hLshape] at hidx
  have hbound : idx < 8 * (d * xs.length) := by simpa [prodShape] using hidx
  have hfullpos : 0 < d * xs.length := Nat.mul_pos hd hK
  let P := idx / (d * xs.length)
  let rem := idx % (d * xs.length)
  let r := rem / d
  let col := rem % d
  have hP : P < 8 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hbound)
  have hrem : rem < d * xs.length := Nat.mod_lt idx hfullpos
  have hr : r < xs.length := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
  have hcol : col < d := Nat.mod_lt rem hd
  have hri : r * d + col = rem := by simpa only [r, col, Nat.mul_comm] using Nat.div_add_mod rem d
  have heq : idx = P * (d * xs.length) + (r * d + col) := by
    rw [hri]
    simpa only [P, rem, Nat.mul_comm] using (Nat.div_add_mod idx (d * xs.length)).symm
  rw [heq, bw_linear_fst_valAt_1_8 _ _ _ o (d * xs.length) hg hx hWshape
    P hP (r * d + col) (by omega)]
  rw [allGatherPrimDimN_dim2_3d_valAt pieces xs.length 1 8 d P r col
    hK hd (by simpa using hP) hr hcol hpiecehead, hpget r hr]
  have hwr : r < ws.length := by omega
  rw [bw_linear_fst_valAt_1_8 _ _ _ o d hg (hxsget r hr) (hwsget r hwr) P hP col hcol]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hv := allGatherPrimDimN1_valAt_g240 ws.length o d ws hW
    ho hd hheadw hwsget j (Finset.mem_range.mp hj) r hwr col hcol
  simpa only [hlen] using hv

end
end TrainVerify.Denote
