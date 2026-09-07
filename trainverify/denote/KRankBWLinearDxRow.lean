import denote.KRankLinearReduction

namespace TrainVerify.Denote
noncomputable section

-- The finite-list sum retains the pairing and order of both shard lists.
private theorem row_foldl_zipWith_eq_sum_range
    (xs ys : List Tensor) (f : Tensor → Tensor → Scalar) (dx dy : Tensor)
    (hlen : ys.length = xs.length) :
    (List.zipWith f xs ys).foldl (fun acc x => acc + x) 0 =
      ∑ r ∈ Finset.range xs.length, f (xs.getD r dx) (ys.getD r dy) := by
  rw [← List.sum_eq_foldl]
  let zs := List.zipWith f xs ys
  have hzlen : zs.length = xs.length := by simp [zs, List.length_zipWith, hlen]
  rw [← hzlen, Finset.sum_range]
  change zs.sum = ∑ i : Fin zs.length, f (xs.getD (↑i) dx) (ys.getD (↑i) dy)
  have hzsum : (∑ i : Fin zs.length, zs[i]) = zs.sum := by
    simpa using Fin.sum_univ_fun_getElem zs id
  rw [← hzsum]
  apply Finset.sum_congr rfl
  intro n _hn
  have hnx : n.val < xs.length := by rw [← hzlen]; exact n.isLt
  have hny : n.val < ys.length := by rw [hlen]; exact hnx
  simp [zs, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hnx, List.getElem?_eq_getElem hny]

-- Keep the output index unchanged: the combined batch/sequence coordinate is
-- independent of the contracted output-channel extent.
private theorem row_bw_linear_fst_valAt
    (g x w : Tensor) (b s o i idx : Nat)
    (hs : 0 < s) (hi : 0 < i)
    (hg : g.shape = [b, s, o]) (hx : x.shape = [b, s, i])
    (hw : w.shape = [o, i]) (hidx : idx < prodShape [b, s, i]) :
    valAt (bw_linear g x w).1 idx =
      ∑ j ∈ Finset.range o,
        valAt g ((idx / (s * i) * s + idx % (s * i) / i) * o + j) *
          valAt w (j * i + idx % (s * i) % i) := by
  conv_lhs => simp only [bw_linear, hg, hx, hw]
  rw [valAt_of_lt _ _ hidx]
  simp only [Tensor.mkShape, if_neg (Nat.mul_pos hs hi).ne', if_neg hi.ne']

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- Row-parallel dX reduction for arbitrary positive rank count and dimensions.
Gradient shards `[b,s,o]` and weight shards `[o,i]` are paired in rank order;
no restriction is placed on their values. The activation is replicated and
contributes only its `[b,s,i]` shape to this component of backward linear. -/
theorem bw_linear_dx_row_reduction_rank3
    (K b s o i : Nat) (gs ws : List Tensor) (x : Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (ho : 0 < o) (hi : 0 < i)
    (hglen : gs.length = K) (hwlen : ws.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, s, o])
    (hws : ∀ w ∈ ws, w.shape = [o, i])
    (hx : x.shape = [b, s, i]) :
    (bw_linear (allGatherPrimDimN 2 K 0 gs) x
      (allGatherPrimDimN 0 K 0 ws)).1 =
      tensorSum (List.zipWith (fun g w => (bw_linear g x w).1) gs ws) := by
  have hlen : ws.length = gs.length := hwlen.trans hglen.symm
  have hheadg : (gs.head?.map (fun t => t.shape)).getD [] = [b, s, o] := by
    cases gs with
    | nil => simp at hglen; omega
    | cons g rest => exact hgs g (List.mem_cons_self ..)
  have hheadw : (ws.head?.map (fun t => t.shape)).getD [] = [o, i] := by
    cases ws with
    | nil => simp at hwlen; omega
    | cons w rest => exact hws w (List.mem_cons_self ..)
  have hGshape : (allGatherPrimDimN 2 K 0 gs).shape = [b, s, o * K] := by
    rw [allGatherPrimDimN_shape 2 K gs [b, s, o] hheadg]
    simp [List.set, List.getD]
  have hWshape : (allGatherPrimDimN 0 K 0 ws).shape = [o * K, i] := by
    rw [allGatherPrimDimN_shape 0 K ws [o, i] hheadw]
    simp [List.set, List.getD]
  have hLshape : (bw_linear (allGatherPrimDimN 2 K 0 gs) x
      (allGatherPrimDimN 0 K 0 ws)).1.shape = [b, s, i] :=
    bw_linear_3d_fst_shape b s (o * K) i _ _ _ hGshape hx hWshape
  have hgr : ∀ r, r < K →
      (gs.getD r (zeroTensor [b, s, o])).shape = [b, s, o] := by
    intro r hr
    have hrlen : r < gs.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrlen]
    exact hgs gs[r] (List.getElem_mem _)
  have hwr : ∀ r, r < K →
      (ws.getD r (zeroTensor [o, i])).shape = [o, i] := by
    intro r hr
    have hrlen : r < ws.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrlen]
    exact hws ws[r] (List.getElem_mem _)
  let pieces := List.zipWith (fun g w => (bw_linear g x w).1) gs ws
  have hpiecehead : (pieces.head?.map (fun t => t.shape)).getD [] = [b, s, i] := by
    cases gs with
    | nil => simp at hglen; omega
    | cons g rest =>
      cases ws with
      | nil => simp at hwlen; omega
      | cons w tail =>
        exact bw_linear_3d_fst_shape b s o i g x w
          (hgs g (List.mem_cons_self ..)) hx (hws w (List.mem_cons_self ..))
  have hsum : tensorSum pieces = allReducePrim K 0 pieces := by
    cases pieces <;> rfl
  change (bw_linear (allGatherPrimDimN 2 K 0 gs) x
    (allGatherPrimDimN 0 K 0 ws)).1 = tensorSum pieces
  rw [hsum]
  have hRshape : (allReducePrim K 0 pieces).shape = [b, s, i] := by
    unfold allReducePrim
    simp only [hpiecehead, Tensor.mkShape]
  apply Tensor.ext (by rw [hLshape, hRshape])
  intro idx hidx
  rw [hLshape] at hidx
  have hflat : idx < b * s * i := by
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  let P := idx / (s * i) * s + idx % (s * i) / i
  let col := idx % (s * i) % i
  have hrow : idx / (s * i) < b := by
    apply Nat.div_lt_of_lt_mul
    calc idx < b * s * i := hflat
      _ = (s * i) * b := by ring
  have hseq : idx % (s * i) / i < s := by
    apply Nat.div_lt_of_lt_mul
    calc idx % (s * i) < s * i := Nat.mod_lt _ (Nat.mul_pos hs hi)
      _ = i * s := by ring
  have hP : P < b * s := by
    calc
      P < idx / (s * i) * s + s := Nat.add_lt_add_left hseq _
      _ = (idx / (s * i) + 1) * s := by ring
      _ ≤ b * s := Nat.mul_le_mul_right s hrow
  have hcol : col < i := Nat.mod_lt _ hi
  rw [row_bw_linear_fst_valAt _ x _ b s (o * K) i idx hs hi hGshape hx hWshape hidx]
  change (∑ j ∈ Finset.range (o * K),
      valAt (allGatherPrimDimN 2 K 0 gs) (P * (o * K) + j) *
        valAt (allGatherPrimDimN 0 K 0 ws) (j * i + col)) = _
  rw [show o * K = K * o by ring, Finset.sum_range_mul_eq_sum_sum]
  have hinner : ∀ r, r < K →
      (∑ j ∈ Finset.range o,
        valAt (allGatherPrimDimN 2 K 0 gs) (P * (K * o) + (r * o + j)) *
          valAt (allGatherPrimDimN 0 K 0 ws) ((r * o + j) * i + col)) =
        valAt (bw_linear (gs.getD r (zeroTensor [b, s, o])) x
          (ws.getD r (zeroTensor [o, i]))).1 idx := by
    intro r hr
    rw [row_bw_linear_fst_valAt _ x _ b s o i idx hs hi (hgr r hr) hx (hwr r hr) hidx]
    change (∑ j ∈ Finset.range o, _) =
      ∑ j ∈ Finset.range o,
        valAt (gs.getD r (zeroTensor [b, s, o])) (P * o + j) *
          valAt (ws.getD r (zeroTensor [o, i])) (j * i + col)
    apply Finset.sum_congr rfl
    intro j hj
    have hjo := Finset.mem_range.mp hj
    have hgv := allGatherPrim_valAt_mul_add_3d K r b s o gs hheadg hK hr P hP j hjo
    rw [← allGatherPrimDimN_2_eq_allGatherPrim_3d K b s o gs hheadg hb hs ho hK] at hgv
    rw [show P * (K * o) + (r * o + j) = P * (o * K) + r * o + j by ring]
    rw [hgv, allGatherPrimDimN0_valAt K o i ws hK ho hi hheadw hwr r hr j hjo col hcol]
  have hRval : valAt (allReducePrim K 0 pieces) idx =
      ∑ r ∈ Finset.range K,
        valAt (bw_linear (gs.getD r (zeroTensor [b, s, o])) x
          (ws.getD r (zeroTensor [o, i]))).1 idx := by
    rw [valAt_of_lt _ _ (by rw [hRshape]; exact hidx)]
    unfold allReducePrim
    simp only [Tensor.mkShape]
    change pieces.foldl (fun acc t => acc + valAt t idx) 0 = _
    dsimp only [pieces]
    rw [← List.foldl_map, List.map_zipWith]
    have hf := row_foldl_zipWith_eq_sum_range gs ws
      (fun g w => valAt (bw_linear g x w).1 idx)
      (zeroTensor [b, s, o]) (zeroTensor [o, i]) hlen
    rw [hglen] at hf
    exact hf
  rw [hRval]
  apply Finset.sum_congr rfl
  intro r hr
  exact hinner r (Finset.mem_range.mp hr)

end
end TrainVerify.Denote
