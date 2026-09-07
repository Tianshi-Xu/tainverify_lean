import denote.KRankLinearGather

namespace TrainVerify.Denote
noncomputable section

set_option maxHeartbeats 500000 in
-- Flatten the batch/sequence pair without fixing either dimension. The
-- activation supplies only the output shape of this backward component.
private theorem column_bw_linear_fst_valAt_rank3
    (g x w : Tensor) (b s o i pre col : Nat)
    (hs : 0 < s) (hi : 0 < i) (hpre : pre < b * s) (hcol : col < i)
    (hg : g.shape = [b, s, o]) (hx : x.shape = [b, s, i])
    (hw : w.shape = [o, i]) :
    valAt (bw_linear g x w).1 (pre * i + col) =
      ∑ j ∈ Finset.range o,
        valAt g (pre * o + j) * valAt w (j * i + col) := by
  have hidx : pre * i + col < (b * s) * i := by
    have hstep : pre * i + col < (pre + 1) * i := by
      rw [Nat.add_mul]; omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right i hpre)
  conv_lhs => simp only [bw_linear, hg, hx, hw]
  rw [valAt_of_lt _ _ (by
    simpa only [Tensor.mkShape, prodShape, List.foldl, Nat.one_mul] using hidx)]
  simp only [Tensor.mkShape]
  have hsi : 0 < s * i := Nat.mul_pos hs hi
  have hpreMod : pre % s < s := Nat.mod_lt pre hs
  have hlocal : (pre % s) * i + col < s * i := by
    calc
      _ < (pre % s) * i + i := Nat.add_lt_add_left hcol _
      _ = (pre % s + 1) * i := by ring
      _ ≤ s * i := Nat.mul_le_mul_right i hpreMod
  have hp : s * (pre / s) + pre % s = pre := Nat.div_add_mod pre s
  have hp' : pre / s * s + pre % s = pre := by
    simpa only [Nat.mul_comm] using hp
  have hdecomp : pre * i + col =
      ((pre % s) * i + col) + (s * i) * (pre / s) := by
    calc
      pre * i + col = (s * (pre / s) + pre % s) * i + col := by rw [hp]
      _ = ((pre % s) * i + col) + (s * i) * (pre / s) := by ring
  have hdivSI : (pre * i + col) / (s * i) = pre / s := by
    rw [hdecomp, Nat.add_mul_div_left _ _ hsi, Nat.div_eq_of_lt hlocal,
      Nat.zero_add]
  have hmodSI : (pre * i + col) % (s * i) = (pre % s) * i + col := by
    rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlocal]
  have hdivI : ((pre % s) * i + col) / i = pre % s := by
    rw [show (pre % s) * i + col = col + i * (pre % s) by ring,
      Nat.add_mul_div_left _ _ hi, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmodI : ((pre % s) * i + col) % i = col := by
    rw [show (pre % s) * i + col = col + i * (pre % s) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  simp only [if_neg hsi.ne', if_neg hi.ne']
  rw [hdivSI, hmodSI, hdivI, hmodI, hp']

set_option maxHeartbeats 500000 in
/-- Column-parallel dX for arbitrary positive rank count and dimensions.
The shared gradient is `[b,s,o]`; ordered weight columns `[o,i]` produce
ordered dX feature shards `[b,s,i]`. No activation-value or output-equality
assumption is required: dX reads the activation shape but not its values. -/
theorem bw_linear_dx_column_allGather_rank3
    (K b s o i : Nat) (g x : Tensor) (xs ws : List Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (ho : 0 < o) (hi : 0 < i)
    (hxlen : xs.length = K) (hwlen : ws.length = K)
    (hg : g.shape = [b, s, o]) (hx : x.shape = [b, s, K * i])
    (hxs : ∀ a ∈ xs, a.shape = [b, s, i])
    (hws : ∀ w ∈ ws, w.shape = [o, i]) :
    (bw_linear g x (allGatherPrimDimN 1 K 0 ws)).1 =
      allGatherPrimDimN 2 K 0
        (List.zipWith (fun a w => (bw_linear g a w).1) xs ws) := by
  have hx' : x.shape = [b, s, i * K] := by
    rw [hx, Nat.mul_comm K i]
  have hheadw : (ws.head?.map (fun t => t.shape)).getD [] = [o, i] := by
    cases ws with
    | nil => simp at hwlen; omega
    | cons w rest => exact hws w (List.mem_cons_self ..)
  have hwsget (r : Nat) (hr : r < K) :
      (ws.getD r (zeroTensor [o, i])).shape = [o, i] := by
    have hwr : r < ws.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwr]
    exact hws ws[r] (List.getElem_mem _)
  have hxsget (r : Nat) (hr : r < K) :
      (xs.getD r (zeroTensor [b, s, i])).shape = [b, s, i] := by
    have hxr : r < xs.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxr]
    exact hxs xs[r] (List.getElem_mem _)
  have hWshape : (allGatherPrimDimN 1 K 0 ws).shape = [o, i * K] := by
    rw [allGatherPrimDimN_shape 1 K ws [o, i] hheadw]
    simp [List.set, List.getD]
  have hLshape : (bw_linear g x (allGatherPrimDimN 1 K 0 ws)).1.shape =
      [b, s, i * K] :=
    bw_linear_3d_fst_shape b s o (i * K) _ _ _ hg hx' hWshape
  let pieces := List.zipWith (fun a w => (bw_linear g a w).1) xs ws
  have hplen : pieces.length = K := by
    simp only [pieces, List.length_zipWith, hxlen, hwlen, min_self]
  have hpget (r : Nat) (hr : r < K) :
      pieces.getD r (zeroTensor [b, s, i]) =
        (bw_linear g (xs.getD r (zeroTensor [b, s, i]))
          (ws.getD r (zeroTensor [o, i]))).1 := by
    have hxr : r < xs.length := by omega
    have hwr : r < ws.length := by omega
    have hpr : r < pieces.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpr]
    simp [pieces, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxr,
      List.getElem?_eq_getElem hwr]
  have hpiecehead : (pieces.head?.map (fun t => t.shape)).getD [] = [b, s, i] := by
    cases xs with
    | nil => simp at hxlen; omega
    | cons a rest =>
      cases ws with
      | nil => simp at hwlen; omega
      | cons w tail =>
        exact bw_linear_3d_fst_shape b s o i g a w hg
          (hxs a (List.mem_cons_self ..)) (hws w (List.mem_cons_self ..))
  have hRshape : (allGatherPrimDimN 2 K 0 pieces).shape = [b, s, i * K] := by
    rw [allGatherPrimDimN_shape 2 K pieces [b, s, i] hpiecehead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLshape, hRshape])
  intro idx hidx
  rw [hLshape] at hidx
  have hbound : idx < (b * s) * (i * K) := by
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  have hfullpos : 0 < i * K := Nat.mul_pos hi hK
  let P := idx / (i * K)
  let rem := idx % (i * K)
  let r := rem / i
  let col := rem % i
  have hP : P < b * s :=
    Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hbound)
  have hrem : rem < i * K := Nat.mod_lt idx hfullpos
  have hr : r < K :=
    Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hrem)
  have hcol : col < i := Nat.mod_lt rem hi
  have hri : r * i + col = rem := by
    simpa only [r, col, Nat.mul_comm] using Nat.div_add_mod rem i
  have heq : idx = P * (i * K) + (r * i + col) := by
    rw [hri]
    simpa only [P, rem, Nat.mul_comm] using (Nat.div_add_mod idx (i * K)).symm
  rw [heq, column_bw_linear_fst_valAt_rank3 _ _ _ b s o (i * K) P
    (r * i + col) hs hfullpos hP (by rw [hri]; exact hrem) hg hx' hWshape]
  rw [allGatherPrimDimN_dim2_3d_valAt pieces K b s i P r col
    hK hi hP hr hcol hpiecehead, hpget r hr]
  rw [column_bw_linear_fst_valAt_rank3 _ _ _ b s o i P col
    hs hi hP hcol hg (hxsget r hr) (hwsget r hr)]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun v : Scalar => valAt g (P * o + j) * v)
    (allGatherPrimDimN1_valAt_g240 K o i ws hK ho hi hheadw hwsget
      j (Finset.mem_range.mp hj) r hr col hcol)

end
end TrainVerify.Denote
