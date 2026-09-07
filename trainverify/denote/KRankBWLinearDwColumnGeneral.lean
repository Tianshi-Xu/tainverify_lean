import denote.KRankLinearGather

namespace TrainVerify.Denote
noncomputable section

set_option maxHeartbeats 500000 in
/-- Ordered input-column shards reconstruct the full rank-3 dW by gathering
along weight dimension 1, with the same output gradient on every rank. -/
theorem bw_linear_dw_column_allGather_rank3
    (K b s o i : Nat) (g : Tensor) (xs ws : List Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (ho : 0 < o) (hi : 0 < i)
    (hlenxs : xs.length = K) (hlenws : ws.length = K)
    (hg : g.shape = [b, s, o])
    (hxs : ∀ t ∈ xs, t.shape = [b, s, i])
    (hws : ∀ t ∈ ws, t.shape = [o, i]) :
    (bw_linear g (allGatherPrimDimN 2 K 0 xs)
      (allGatherPrimDimN 1 K 0 ws)).2 =
      allGatherPrimDimN 1 K 0
        (List.zipWith (fun x w => (bw_linear g x w).2) xs ws) := by
  have hXpos : 0 < xs.length := by omega
  have hWpos : 0 < ws.length := by omega
  have hheadx : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, i] := by
    cases xs with
    | nil => simp at hXpos
    | cons a rest => simpa using hxs a (by simp)
  have hheadw : (ws.head?.map (fun t => t.shape)).getD [] = [o, i] := by
    cases ws with
    | nil => simp at hWpos
    | cons w rest => simpa using hws w (by simp)
  have hwsget (r : Nat) (hr : r < K) :
      (ws.getD r (zeroTensor [o, i])).shape = [o, i] := by
    have hrlen : r < ws.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrlen]
    exact hws ws[r] (List.getElem_mem _)
  have hxsget (r : Nat) (hr : r < K) :
      (xs.getD r (zeroTensor [b, s, i])).shape = [b, s, i] := by
    have hrlen : r < xs.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrlen]
    exact hxs xs[r] (List.getElem_mem _)
  have hXshape : (allGatherPrimDimN 2 K 0 xs).shape = [b, s, i * K] := by
    rw [allGatherPrimDimN_shape 2 K xs [b, s, i] hheadx]
    simp [List.set, List.getD]
  have hWshape : (allGatherPrimDimN 1 K 0 ws).shape = [o, i * K] := by
    rw [allGatherPrimDimN_shape 1 K ws [o, i] hheadw]
    simp [List.set, List.getD]
  have hLshape : (bw_linear g (allGatherPrimDimN 2 K 0 xs)
      (allGatherPrimDimN 1 K 0 ws)).2.shape = [o, i * K] :=
    bw_linear_3d_snd_shape b s o (i * K) _ _ _ hg hXshape hWshape
  let pieces := List.zipWith (fun x w => (bw_linear g x w).2) xs ws
  have hplen : pieces.length = K := by
    simp [pieces, List.length_zipWith, hlenxs, hlenws]
  have hpget (r : Nat) (hr : r < K) :
      pieces.getD r (zeroTensor [o, i]) =
        (bw_linear g (xs.getD r (zeroTensor [b, s, i]))
          (ws.getD r (zeroTensor [o, i]))).2 := by
    have hxr : r < xs.length := by omega
    have hwr : r < ws.length := by omega
    have hpr : r < pieces.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpr]
    simp [pieces, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxr,
      List.getElem?_eq_getElem hwr]
  have hpshape (r : Nat) (hr : r < K) :
      (pieces.getD r (zeroTensor [o, i])).shape = [o, i] := by
    rw [hpget r hr]
    exact bw_linear_3d_snd_shape b s o i _ _ _ hg (hxsget r hr) (hwsget r hr)
  have hpiecehead : (pieces.head?.map (fun t => t.shape)).getD [] = [o, i] := by
    cases xs with
    | nil => simp at hXpos
    | cons a rest =>
      cases ws with
      | nil => simp at hWpos
      | cons w wrest =>
        simp [pieces, bw_linear_3d_snd_shape b s o i g a w hg
          (hxs a (by simp)) (hws w (by simp))]
  have hRshape : (allGatherPrimDimN 1 K 0 pieces).shape = [o, i * K] := by
    rw [allGatherPrimDimN_shape 1 K pieces [o, i] hpiecehead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLshape, hRshape])
  intro idx hidx
  rw [hLshape] at hidx
  have hbound : idx < o * (i * K) := by simpa [prodShape] using hidx
  have hfullpos : 0 < i * K := Nat.mul_pos hi hK
  let P := idx / (i * K)
  let rem := idx % (i * K)
  let r := rem / i
  let col := rem % i
  have hP : P < o := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hbound)
  have hrem : rem < i * K := Nat.mod_lt idx hfullpos
  have hr : r < K := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
  have hcol : col < i := Nat.mod_lt rem hi
  have hri : r * i + col = rem := by
    simpa only [r, col, Nat.mul_comm] using Nat.div_add_mod rem i
  have heq : idx = P * (i * K) + (r * i + col) := by
    rw [hri]
    simpa only [P, rem, Nat.mul_comm] using (Nat.div_add_mod idx (i * K)).symm
  rw [heq, bw_linear_dw_valAt3d _ _ _ b s o (i * K) hg hXshape hWshape
    P hP (r * i + col) (by omega)]
  rw [allGatherPrimDimN1_valAt_g240 K o i pieces hK ho hi hpiecehead hpshape
    P hP r hr col hcol, hpget r hr]
  rw [bw_linear_dw_valAt3d _ _ _ b s o i hg (hxsget r hr) (hwsget r hr) P hP col hcol]
  apply Finset.sum_congr rfl
  intro p hp
  have hpbound : p < b * s := Finset.mem_range.mp hp
  congr 1
  exact allGatherPrimDimN_dim2_3d_valAt xs K b s i p r col
    hK hi hpbound hr hcol hheadx

end
end TrainVerify.Denote
