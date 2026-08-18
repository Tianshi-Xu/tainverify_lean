import denote.Denote

namespace TrainVerify.Denote

noncomputable section

open scoped BigOperators

/-- A canonical value read through a dim-1 gather of `[b, s, d]` shards.
The global coordinates `(q, r*s+p, j)` select rank `r` and the local
coordinates `(q,p,j)`. -/
theorem allGatherPrimDimN_dim1_3d_valAt
    (xs : List Tensor) (K b s d q r p j : Nat)
    (hK : 0 < K) (hs : 0 < s) (hd : 0 < d)
    (hq : q < b) (hr : r < K) (hp : p < s) (hj : j < d)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, d]) :
    valAt (allGatherPrimDimN 1 K 0 xs)
        ((q * (s * K) + (r * s + p)) * d + j) =
      valAt (xs.getD r (zeroTensor [b, s, d])) ((q * s + p) * d + j) := by
  have hfullShape : (allGatherPrimDimN 1 K 0 xs).shape = [b, s * K, d] := by
    rw [allGatherPrimDimN_shape 1 K xs [b, s, d] hhead]
    simp [List.set, List.getD]
  have hlocal : r * s + p < s * K := by
    have hstep : r * s + p < (r + 1) * s := by
      rw [Nat.add_mul]
      omega
    have hr1 : r + 1 ≤ K := by omega
    have hmul := Nat.mul_le_mul_right s hr1
    rw [Nat.mul_comm K s] at hmul
    exact lt_of_lt_of_le hstep hmul
  have hrow : q * (s * K) + (r * s + p) < b * (s * K) := by
    have hstep : q * (s * K) + (r * s + p) < (q + 1) * (s * K) := by
      rw [Nat.add_mul]
      omega
    have hq1 : q + 1 ≤ b := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right (s * K) hq1)
  have hidx : (q * (s * K) + (r * s + p)) * d + j < b * (s * K) * d := by
    have hstep : (q * (s * K) + (r * s + p)) * d + j <
        (q * (s * K) + (r * s + p) + 1) * d := by
      calc
        _ < (q * (s * K) + (r * s + p)) * d + d :=
          Nat.add_lt_add_left hj _
        _ = _ := by ring
    have hrow1 : q * (s * K) + (r * s + p) + 1 ≤ b * (s * K) := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d hrow1)
  have hidxProd : (q * (s * K) + (r * s + p)) * d + j <
      prodShape (allGatherPrimDimN 1 K 0 xs).shape := by
    rw [hfullShape]
    simpa [prodShape, Nat.mul_assoc] using hidx
  rw [valAt_of_lt _ _ hidxProd]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl]
  have hSK : 0 < s * K := Nat.mul_pos hs hK
  have hfullStride : 0 < (s * K) * d := Nat.mul_pos hSK hd
  have hrem : (r * s + p) * d + j < (s * K) * d := by
    have hstep : (r * s + p) * d + j < (r * s + p + 1) * d := by
      calc
        _ < (r * s + p) * d + d := Nat.add_lt_add_left hj _
        _ = _ := by ring
    have hlocal1 : r * s + p + 1 ≤ s * K := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d hlocal1)
  have hpre : ((q * (s * K) + (r * s + p)) * d + j) / ((s * K) * d) = q := by
    rw [show (q * (s * K) + (r * s + p)) * d + j =
        ((r * s + p) * d + j) + ((s * K) * d) * q by ring]
    rw [Nat.add_mul_div_left _ _ hfullStride, Nat.div_eq_of_lt hrem, Nat.zero_add]
  have hremEq : ((q * (s * K) + (r * s + p)) * d + j) % ((s * K) * d) =
      (r * s + p) * d + j := by
    rw [show (q * (s * K) + (r * s + p)) * d + j =
        ((r * s + p) * d + j) + ((s * K) * d) * q by ring]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem]
  have hjFull : ((r * s + p) * d + j) / d = r * s + p := by
    rw [show (r * s + p) * d + j = j + d * (r * s + p) by ring,
      Nat.add_mul_div_left j (r * s + p) hd, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hk : ((r * s + p) * d + j) % d = j := by
    rw [show (r * s + p) * d + j = j + d * (r * s + p) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hrank : (r * s + p) / s = r := by
    rw [show r * s + p = p + s * r by ring,
      Nat.add_mul_div_left p r hs, Nat.div_eq_of_lt hp, Nat.zero_add]
  have hpLocal : (r * s + p) % s = p := by
    rw [show r * s + p = p + s * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Nat.one_mul,
    if_neg (Nat.ne_of_gt hfullStride), if_neg (Nat.ne_of_gt hd),
    if_neg (Nat.ne_of_gt hs), hpre, hremEq, hjFull, hk, hrank, hpLocal]
  congr 1
  ring

/-- `fw_layernorm` at canonical coordinates of a 3D tensor.  No shape
restriction is imposed on `gamma` or `beta`; only their first `d` values are
observed, matching the denotation's valid LayerNorm parameter contract. -/
theorem fw_layernorm_valAt_3d
    (x gamma beta : Tensor) (b s d q p j : Nat)
    (hs : 0 < s) (hd : 0 < d) (hq : q < b) (hp : p < s) (hj : j < d)
    (hx : x.shape = [b, s, d]) :
    valAt (fw_layernorm x gamma beta) ((q * s + p) * d + j) =
      let row := q * s + p
      let mean := layerNormMeanAt x row d
      let var := layerNormVarAt x row d mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      ((valAt x (row * d + j) - mean) * invStd) * valAt gamma j + valAt beta j := by
  have hrow : q * s + p < b * s := by
    have hstep : q * s + p < (q + 1) * s := by
      rw [Nat.add_mul]
      omega
    have hq1 : q + 1 ≤ b := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right s hq1)
  have hidx : (q * s + p) * d + j < b * s * d := by
    have hstep : (q * s + p) * d + j < (q * s + p + 1) * d := by
      calc
        _ < (q * s + p) * d + d := Nat.add_lt_add_left hj _
        _ = _ := by ring
    have hrow1 : q * s + p + 1 ≤ b * s := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d hrow1)
  rw [fw_layernorm_eq x gamma beta d [s, b] (by rw [hx]; rfl)]
  rw [valAt_of_lt _ _ (by simpa [Tensor.mkShape, hx, prodShape, Nat.mul_assoc] using hidx)]
  simp only [Tensor.mkShape]
  have hrow : ((q * s + p) * d + j) / d = q * s + p := by
    rw [show (q * s + p) * d + j = j + d * (q * s + p) by ring,
      Nat.add_mul_div_left j (q * s + p) hd, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hj' : ((q * s + p) * d + j) % d = j := by
    rw [show (q * s + p) * d + j = j + d * (q * s + p) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [hrow, hj']

/-- Last-dimension LayerNorm mean is preserved by gathering the orthogonal
sequence dimension. -/
theorem layerNormMeanAt_allGatherPrimDimN_dim1_3d
    (xs : List Tensor) (K b s d q r p : Nat)
    (hK : 0 < K) (hs : 0 < s) (hd : 0 < d)
    (hq : q < b) (hr : r < K) (hp : p < s)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, d]) :
    layerNormMeanAt (allGatherPrimDimN 1 K 0 xs) (q * (s * K) + (r * s + p)) d =
      layerNormMeanAt (xs.getD r (zeroTensor [b, s, d])) (q * s + p) d := by
  unfold layerNormMeanAt
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  exact allGatherPrimDimN_dim1_3d_valAt xs K b s d q r p j hK hs hd hq hr hp hj hhead

/-- Last-dimension LayerNorm variance is preserved by gathering the orthogonal
sequence dimension. -/
theorem layerNormVarAt_allGatherPrimDimN_dim1_3d
    (xs : List Tensor) (K b s d q r p : Nat) (mean : Scalar)
    (hK : 0 < K) (hs : 0 < s) (hd : 0 < d)
    (hq : q < b) (hr : r < K) (hp : p < s)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, d]) :
    layerNormVarAt (allGatherPrimDimN 1 K 0 xs) (q * (s * K) + (r * s + p)) d mean =
      layerNormVarAt (xs.getD r (zeroTensor [b, s, d])) (q * s + p) d mean := by
  unfold layerNormVarAt
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [allGatherPrimDimN_dim1_3d_valAt xs K b s d q r p j hK hs hd hq hr hp hj hhead]

/-- For any positive rank count `K`, 3D LayerNorm over the last dimension
commutes with gathering `[b,s,d]` shards along dimension 1 into
`[b,s*K,d]`.  `gamma` and `beta` have the generic valid LayerNorm shape `[d]`. -/
theorem fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d
    (K b s d : Nat) (xs : List Tensor) (gamma beta : Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hd : 0 < d)
    (hlen : xs.length = K)
    (hshape : ∀ x ∈ xs, x.shape = [b, s, d])
    (hgamma : gamma.shape = [d]) (hbeta : beta.shape = [d]) :
    fw_layernorm (allGatherPrimDimN 1 K 0 xs) gamma beta =
      allGatherPrimDimN 1 K 0 (xs.map (fun x => fw_layernorm x gamma beta)) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  obtain ⟨x0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hx0 : x0.shape = [b, s, d] := hshape x0 (by simp)
  have hhead : (((x0 :: rest).head?.map (fun t => t.shape)).getD []) = [b, s, d] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hx0
  have hfullShape : (allGatherPrimDimN 1 K 0 (x0 :: rest)).shape = [b, s * K, d] := by
    rw [allGatherPrimDimN_shape 1 K (x0 :: rest) [b, s, d] hhead]
    simp [List.set, List.getD]
  have hmapHead :
      ((((x0 :: rest).map (fun x => fw_layernorm x gamma beta)).head?.map
        (fun t => t.shape)).getD []) = [b, s, d] := by
    simp only [List.map, List.head?, Option.map, Option.getD]
    unfold fw_layernorm
    rw [hx0]
    rfl
  have hrhsShape :
      (allGatherPrimDimN 1 K 0 ((x0 :: rest).map (fun x => fw_layernorm x gamma beta))).shape =
        [b, s * K, d] := by
    rw [allGatherPrimDimN_shape 1 K _ [b, s, d] hmapHead]
    simp [List.set, List.getD]
  have hlhsShape :
      (fw_layernorm (allGatherPrimDimN 1 K 0 (x0 :: rest)) gamma beta).shape =
        [b, s * K, d] := by
    rw [fw_layernorm_eq (allGatherPrimDimN 1 K 0 (x0 :: rest)) gamma beta d
      [s * K, b] (by rw [hfullShape]; rfl)]
    simp only [Tensor.mkShape]
    exact hfullShape
  apply Tensor.ext
  · rw [hlhsShape, hrhsShape]
  · intro idx hidx
    have hidxBound : idx < b * (s * K) * d := by
      rw [hlhsShape] at hidx
      simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hidx
    set j := idx % d with hjDef
    set row := idx / d with hrowDef
    have hj : j < d := by rw [hjDef]; exact Nat.mod_lt _ hd
    have hrow : row < b * (s * K) := by
      rw [hrowDef, Nat.div_lt_iff_lt_mul hd]
      simpa [Nat.mul_assoc] using hidxBound
    set q := row / (s * K) with hqDef
    set g := row % (s * K) with hgDef
    have hSK : 0 < s * K := Nat.mul_pos hs hK
    have hq : q < b := by
      rw [hqDef, Nat.div_lt_iff_lt_mul hSK]
      exact hrow
    have hg : g < s * K := by rw [hgDef]; exact Nat.mod_lt _ hSK
    set r := g / s with hrDef
    set p := g % s with hpDef
    have hr : r < K := by
      rw [hrDef, Nat.div_lt_iff_lt_mul hs]
      simpa only [Nat.mul_comm] using hg
    have hp : p < s := by rw [hpDef]; exact Nat.mod_lt _ hs
    have hrowEq : row = q * (s * K) + (r * s + p) := by
      have h1 := (Nat.div_add_mod row (s * K)).symm
      have h2 := (Nat.div_add_mod g s).symm
      rw [← hqDef, ← hgDef] at h1
      rw [← hrDef, ← hpDef] at h2
      calc
        row = s * K * q + g := h1
        _ = q * (s * K) + g := by ring
        _ = q * (s * K) + (r * s + p) := by rw [h2]; ring
    have hidxEq : idx = (q * (s * K) + (r * s + p)) * d + j := by
      have h := (Nat.div_add_mod idx d).symm
      rw [← hrowDef, ← hjDef] at h
      calc
        idx = d * row + j := h
        _ = row * d + j := by ring
        _ = (q * (s * K) + (r * s + p)) * d + j := by rw [hrowEq]
    rw [hidxEq]
    have hxr : ((x0 :: rest).getD r (zeroTensor [b, s, d])).shape = [b, s, d] := by
      have hrLen : r < (x0 :: rest).length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrLen]
      simp only [Option.getD_some]
      exact hshape ((x0 :: rest)[r]) (List.getElem_mem hrLen)
    rw [fw_layernorm_valAt_3d (allGatherPrimDimN 1 K 0 (x0 :: rest)) gamma beta
          b (s * K) d q (r * s + p) j hSK hd hq (by nlinarith) hj hfullShape]
    rw [allGatherPrimDimN_dim1_3d_valAt
          ((x0 :: rest).map (fun x => fw_layernorm x gamma beta)) K b s d q r p j
          hK hs hd hq hr hp hj hmapHead]
    have hrLen : r < (x0 :: rest).length := by omega
    have hmapGet :
        ((x0 :: rest).map (fun x => fw_layernorm x gamma beta)).getD r
            (zeroTensor [b, s, d]) =
          fw_layernorm ((x0 :: rest).getD r (zeroTensor [b, s, d])) gamma beta := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hrLen, Option.map_some, Option.getD_some]
    rw [hmapGet]
    rw [fw_layernorm_valAt_3d ((x0 :: rest).getD r (zeroTensor [b, s, d])) gamma beta
          b s d q p j hs hd hq hp hj hxr]
    dsimp only
    rw [allGatherPrimDimN_dim1_3d_valAt (x0 :: rest) K b s d q r p j
          hK hs hd hq hr hp hj hhead]
    rw [layerNormMeanAt_allGatherPrimDimN_dim1_3d (x0 :: rest) K b s d q r p
          hK hs hd hq hr hp hhead]
    rw [layerNormVarAt_allGatherPrimDimN_dim1_3d (x0 :: rest) K b s d q r p _
          hK hs hd hq hr hp hhead]

end

end TrainVerify.Denote
