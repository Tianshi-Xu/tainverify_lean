import denote.KRankLayernormGather

namespace TrainVerify.Denote
noncomputable section

-- Row-locality is the semantic reason a sequence-axis gather commutes with dX.
private theorem bw_layernorm_dx_row_congr
    (g x g' x' gamma beta : Tensor) (b s b' s' d row row' j : Nat)
    (hx : x.shape = [b, s, d]) (hx' : x'.shape = [b', s', d])
    (hd : 0 < d) (hr : row < b * s) (hr' : row' < b' * s') (hj : j < d)
    (hg : ∀ k < d, valAt g (row * d + k) = valAt g' (row' * d + k))
    (hval : ∀ k < d, valAt x (row * d + k) = valAt x' (row' * d + k)) :
    valAt (bw_layernorm g x gamma beta).1 (row * d + j) =
      valAt (bw_layernorm g' x' gamma beta).1 (row' * d + j) := by
  have hm : layerNormMeanAt x row d = layerNormMeanAt x' row' d := by
    unfold layerNormMeanAt
    congr 1
    exact Finset.sum_congr rfl (fun k hk => hval k (Finset.mem_range.mp hk))
  have hv : layerNormVarAt x row d (layerNormMeanAt x row d) =
      layerNormVarAt x' row' d (layerNormMeanAt x' row' d) := by
    rw [hm]
    unfold layerNormVarAt
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hval k (Finset.mem_range.mp hk)]
  have hbound : row * d + j < b * s * d := by nlinarith
  have hbound' : row' * d + j < b' * s' * d := by nlinarith
  rw [bw_layernorm_dx_eq g x gamma beta d [s, b] (by rw [hx]; rfl),
    bw_layernorm_dx_eq g' x' gamma beta d [s', b'] (by rw [hx']; rfl)]
  rw [valAt_of_lt _ _ (by simpa [Tensor.mkShape, hx, prodShape, Nat.mul_assoc] using hbound),
    valAt_of_lt _ _ (by simpa [Tensor.mkShape, hx', prodShape, Nat.mul_assoc] using hbound')]
  have hdiv : (row * d + j) / d = row := by
    rw [Nat.mul_comm row d, Nat.mul_add_div hd, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hdiv' : (row' * d + j) / d = row' := by
    rw [Nat.mul_comm row' d, Nat.mul_add_div hd, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (row * d + j) % d = j := by
    rw [Nat.mul_comm row d, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have hmod' : (row' * d + j) % d = j := by
    rw [Nat.mul_comm row' d, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  simp only [Tensor.mkShape, hdiv, hdiv', hmod, hmod']
  rw [hv, hm, hg j hj, hval j hj]
  have hsum : (∑ k ∈ Finset.range d, valAt g (row * d + k) * valAt gamma k) =
      ∑ k ∈ Finset.range d, valAt g' (row' * d + k) * valAt gamma k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hg k (Finset.mem_range.mp hk)]
  rw [hsum]
  congr 3
  apply Finset.sum_congr rfl
  intro k hk
  rw [hg k (Finset.mem_range.mp hk), hval k (Finset.mem_range.mp hk)]

-- K, batch, local sequence length, and feature width are symbolic. The two
-- operand lists have the same ordered rank interpretation, expressed by zipWith.
set_option maxHeartbeats 800000 in
theorem bw_layernorm_dx_allGatherPrimDimN_dim1_3d
    (K b s d : Nat) (gs xs : List Tensor) (gamma beta : Tensor)
    (hK : 0 < K) (_hb : 0 < b) (hs : 0 < s) (hd : 0 < d)
    (hglen : gs.length = K) (hxlen : xs.length = K)
    (hgsh : ∀ g ∈ gs, g.shape = [b, s, d])
    (hxsh : ∀ x ∈ xs, x.shape = [b, s, d]) :
    (bw_layernorm (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) gamma beta).1 =
      allGatherPrimDimN 1 K 0
        (List.zipWith (fun g x => (bw_layernorm g x gamma beta).1) gs xs) := by
  have hgne : gs ≠ [] := by intro h; simp [h] at hglen; omega
  have hxne : xs ≠ [] := by intro h; simp [h] at hxlen; omega
  have hheadg : (gs.head?.map (fun t => t.shape)).getD [] = [b, s, d] := by
    obtain ⟨g, rest, rfl⟩ := List.exists_cons_of_ne_nil hgne
    exact hgsh g (by simp)
  have hheadx : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, d] := by
    obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hxne
    exact hxsh x (by simp)
  have hfull : (allGatherPrimDimN 1 K 0 xs).shape = [b, s * K, d] := by
    rw [allGatherPrimDimN_shape 1 K xs [b, s, d] hheadx]
    simp [List.set, List.getD]
  let pieces := List.zipWith (fun g x => (bw_layernorm g x gamma beta).1) gs xs
  have hpiecehead : (pieces.head?.map (fun t => t.shape)).getD [] = [b, s, d] := by
    obtain ⟨g, gr, rfl⟩ := List.exists_cons_of_ne_nil hgne
    obtain ⟨x, xr, rfl⟩ := List.exists_cons_of_ne_nil hxne
    change (bw_layernorm g x gamma beta).1.shape = [b, s, d]
    rw [bw_layernorm_dx_shape g x gamma beta d [s, b] (by rw [hxsh x (by simp)]; rfl)]
    exact hxsh x (by simp)
  have hlhs : (bw_layernorm (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) gamma beta).1.shape = [b, s * K, d] := by
    rw [bw_layernorm_dx_shape _ _ _ _ d [s * K, b] (by rw [hfull]; rfl)]
    exact hfull
  have hrhs : (allGatherPrimDimN 1 K 0 pieces).shape = [b, s * K, d] := by
    rw [allGatherPrimDimN_shape 1 K pieces [b, s, d] hpiecehead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs, hrhs])
  intro idx hidx
  have hidxBound : idx < b * (s * K) * d := by
    rw [hlhs] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hidx
  let j := idx % d
  let row := idx / d
  have hj : j < d := Nat.mod_lt _ hd
  have hrow : row < b * (s * K) := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    exact hidxBound
  let q := row / (s * K)
  let t := row % (s * K)
  have hSK : 0 < s * K := Nat.mul_pos hs hK
  have hq : q < b := (Nat.div_lt_iff_lt_mul hSK).mpr hrow
  have ht : t < s * K := Nat.mod_lt _ hSK
  let r := t / s
  let p := t % s
  have hr : r < K := (Nat.div_lt_iff_lt_mul hs).mpr (by simpa [Nat.mul_comm] using ht)
  have hp : p < s := Nat.mod_lt _ hs
  have heq : idx = (q * (s * K) + (r * s + p)) * d + j := by
    have h1 := Nat.div_add_mod idx d
    have h2 := Nat.div_add_mod row (s * K)
    have h3 := Nat.div_add_mod t s
    change d * row + j = idx at h1
    change s * K * q + t = row at h2
    change s * r + p = t at h3
    rw [← h1, ← h2, ← h3]
    ring
  have hgr : r < gs.length := by rw [hglen]; exact hr
  have hxr : r < xs.length := by rw [hxlen]; exact hr
  have hxlocal : (xs.getD r (zeroTensor [b, s, d])).shape = [b, s, d] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxr]
    exact hxsh xs[r] (List.getElem_mem hxr)
  have hget : pieces.getD r (zeroTensor [b, s, d]) =
      (bw_layernorm (gs.getD r (zeroTensor [b, s, d]))
        (xs.getD r (zeroTensor [b, s, d])) gamma beta).1 := by
    have hrp : r < pieces.length := by simp only [pieces, List.length_zipWith]; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrp,
      List.getElem?_eq_getElem hgr, List.getElem?_eq_getElem hxr, Option.getD_some]
    exact List.getElem_zipWith
  rw [heq, allGatherPrimDimN_dim1_3d_valAt pieces K b s d q r p j
    hK hs hd hq hr hp hj hpiecehead, hget]
  apply bw_layernorm_dx_row_congr _ _ _ _ gamma beta b (s * K) b s d
    (q * (s * K) + (r * s + p)) (q * s + p) j hfull hxlocal hd
  · have hlocal : r * s + p < s * K := by nlinarith
    nlinarith
  · nlinarith
  · exact hj
  · intro k hk
    exact allGatherPrimDimN_dim1_3d_valAt gs K b s d q r p k hK hs hd hq hr hp hk hheadg
  · intro k hk
    exact allGatherPrimDimN_dim1_3d_valAt xs K b s d q r p k hK hs hd hq hr hp hk hheadx

end
end TrainVerify.Denote
