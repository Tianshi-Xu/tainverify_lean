import denote.KRankLinearGather

namespace TrainVerify.Denote
noncomputable section

/-- Ordered input-column shards reconstruct dW without a rank reduction. -/
theorem bw_linear_dw_input_allGatherPrimDimN_dim2_rank3
    (g : Tensor) (xs ws : List Tensor) (o d : Nat)
    (ho : 0 < o) (hd : 0 < d)
    (hne : xs ≠ []) (hlen : ws.length = xs.length)
    (hg : g.shape = [1, 8, o])
    (hxs : ∀ t ∈ xs, t.shape = [1, 8, d])
    (hws : ∀ t ∈ ws, t.shape = [o, d]) :
    (bw_linear g (allGatherPrimDimN 2 xs.length 0 xs)
      (allGatherPrimDimN 1 ws.length 0 ws)).2 =
      allGatherPrimDimN 1 xs.length 0
        (List.zipWith (fun a w => (bw_linear g a w).2) xs ws) := by
  have hK : 0 < xs.length := List.length_pos_iff.mpr hne
  have hW : 0 < ws.length := by omega
  have hheadx : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, d] := by
    cases xs with
    | nil => simp at hK
    | cons a rest => simpa using hxs a (by simp)
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
  have hXshape : (allGatherPrimDimN 2 xs.length 0 xs).shape = [1, 8, d * xs.length] := by
    rw [allGatherPrimDimN_shape 2 xs.length xs [1, 8, d] hheadx]
    simp [List.set, List.getD]
  have hWshape : (allGatherPrimDimN 1 ws.length 0 ws).shape = [o, d * xs.length] := by
    rw [allGatherPrimDimN_shape 1 ws.length ws [o, d] hheadw]
    simp [List.set, List.getD, hlen]
  have hLshape : (bw_linear g (allGatherPrimDimN 2 xs.length 0 xs)
      (allGatherPrimDimN 1 ws.length 0 ws)).2.shape = [o, d * xs.length] :=
    bw_linear_3d_snd_shape 1 8 o (d * xs.length) _ _ _ hg hXshape hWshape
  let pieces := List.zipWith (fun a w => (bw_linear g a w).2) xs ws
  have hplen : pieces.length = xs.length := by simp [pieces, List.length_zipWith, hlen]
  have hpget (r : Nat) (hr : r < xs.length) :
      pieces.getD r (zeroTensor [o, d]) =
        (bw_linear g (xs.getD r (zeroTensor [1, 8, d]))
          (ws.getD r (zeroTensor [o, d]))).2 := by
    have hwr : r < ws.length := by omega
    have hpr : r < pieces.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpr]
    simp [pieces, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr,
      List.getElem?_eq_getElem hwr]
  have hpshape (r : Nat) (hr : r < xs.length) :
      (pieces.getD r (zeroTensor [o, d])).shape = [o, d] := by
    rw [hpget r hr]
    exact bw_linear_3d_snd_shape 1 8 o d _ _ _ hg (hxsget r hr) (hwsget r (by omega))
  have hpiecehead : (pieces.head?.map (fun t => t.shape)).getD [] = [o, d] := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons a rest =>
      cases ws with
      | nil => simp at hlen
      | cons w wrest =>
        simp [pieces, bw_linear_3d_snd_shape 1 8 o d g a w hg
          (hxs a (by simp)) (hws w (by simp))]
  have hRshape : (allGatherPrimDimN 1 xs.length 0 pieces).shape = [o, d * xs.length] := by
    rw [allGatherPrimDimN_shape 1 xs.length pieces [o, d] hpiecehead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLshape, hRshape])
  intro idx hidx
  rw [hLshape] at hidx
  have hbound : idx < o * (d * xs.length) := by simpa [prodShape] using hidx
  have hfullpos : 0 < d * xs.length := Nat.mul_pos hd hK
  let P := idx / (d * xs.length)
  let rem := idx % (d * xs.length)
  let r := rem / d
  let col := rem % d
  have hP : P < o := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hbound)
  have hrem : rem < d * xs.length := Nat.mod_lt idx hfullpos
  have hr : r < xs.length := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
  have hcol : col < d := Nat.mod_lt rem hd
  have hri : r * d + col = rem := by simpa only [r, col, Nat.mul_comm] using Nat.div_add_mod rem d
  have heq : idx = P * (d * xs.length) + (r * d + col) := by
    rw [hri]
    simpa only [P, rem, Nat.mul_comm] using (Nat.div_add_mod idx (d * xs.length)).symm
  rw [heq, bw_linear_dw_valAt3d _ _ _ 1 8 o (d * xs.length) hg hXshape hWshape
    P hP (r * d + col) (by omega)]
  rw [allGatherPrimDimN1_valAt_g240 xs.length o d pieces hK ho hd hpiecehead hpshape
    P hP r hr col hcol, hpget r hr]
  rw [bw_linear_dw_valAt3d _ _ _ 1 8 o d hg (hxsget r hr) (hwsget r (by omega)) P hP col hcol]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  exact allGatherPrimDimN_dim2_3d_valAt xs xs.length 1 8 d p r col
    hK hd (Finset.mem_range.mp hp) hr hcol hheadx

end
end TrainVerify.Denote
