import denote.RelationCompiler

namespace TrainVerify.Denote

noncomputable section

open scoped BigOperators

/-- A canonical value read through a dim-2 gather of rank-4 shards.  The
flattened prefix coordinate `q` ranges over the first two dimensions. -/
theorem allGatherPrimDimN_dim2_rank4_valAt
    (xs : List Tensor) (K d0 d1 d2 d3 q r p j : Nat)
    (hK : 0 < K) (hd2 : 0 < d2) (hd3 : 0 < d3)
    (hq : q < d0 * d1) (hr : r < K) (hp : p < d2) (hj : j < d3)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0, d1, d2, d3]) :
    valAt (allGatherPrimDimN 2 K 0 xs)
        ((q * (d2 * K) + (r * d2 + p)) * d3 + j) =
      valAt (xs.getD r (zeroTensor [d0, d1, d2, d3]))
        ((q * d2 + p) * d3 + j) := by
  have hfullShape : (allGatherPrimDimN 2 K 0 xs).shape = [d0, d1, d2 * K, d3] := by
    rw [allGatherPrimDimN_shape 2 K xs [d0, d1, d2, d3] hhead]
    simp [List.set, List.getD]
  have hlocal : r * d2 + p < d2 * K := by
    have hstep : r * d2 + p < (r + 1) * d2 := by
      rw [Nat.add_mul]
      omega
    have hr1 : r + 1 ≤ K := by omega
    have hmul := Nat.mul_le_mul_right d2 hr1
    rw [Nat.mul_comm K d2] at hmul
    exact lt_of_lt_of_le hstep hmul
  have hrow : q * (d2 * K) + (r * d2 + p) < (d0 * d1) * (d2 * K) := by
    have hstep : q * (d2 * K) + (r * d2 + p) < (q + 1) * (d2 * K) := by
      rw [Nat.add_mul]
      omega
    have hq1 : q + 1 ≤ d0 * d1 := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right (d2 * K) hq1)
  have hidx : (q * (d2 * K) + (r * d2 + p)) * d3 + j <
      (d0 * d1) * (d2 * K) * d3 := by
    have hstep : (q * (d2 * K) + (r * d2 + p)) * d3 + j <
        (q * (d2 * K) + (r * d2 + p) + 1) * d3 := by
      calc
        _ < (q * (d2 * K) + (r * d2 + p)) * d3 + d3 :=
          Nat.add_lt_add_left hj _
        _ = _ := by ring
    have hrow1 : q * (d2 * K) + (r * d2 + p) + 1 ≤
        (d0 * d1) * (d2 * K) := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d3 hrow1)
  have hidxProd : (q * (d2 * K) + (r * d2 + p)) * d3 + j <
      prodShape (allGatherPrimDimN 2 K 0 xs).shape := by
    rw [hfullShape]
    simpa [prodShape, Nat.mul_assoc] using hidx
  rw [valAt_of_lt _ _ hidxProd]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl]
  have hD2K : 0 < d2 * K := Nat.mul_pos hd2 hK
  have hfullStride : 0 < (d2 * K) * d3 := Nat.mul_pos hD2K hd3
  have hrem : (r * d2 + p) * d3 + j < (d2 * K) * d3 := by
    have hstep : (r * d2 + p) * d3 + j < (r * d2 + p + 1) * d3 := by
      calc
        _ < (r * d2 + p) * d3 + d3 := Nat.add_lt_add_left hj _
        _ = _ := by ring
    have hlocal1 : r * d2 + p + 1 ≤ d2 * K := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d3 hlocal1)
  have hpre : ((q * (d2 * K) + (r * d2 + p)) * d3 + j) /
      ((d2 * K) * d3) = q := by
    rw [show (q * (d2 * K) + (r * d2 + p)) * d3 + j =
        ((r * d2 + p) * d3 + j) + ((d2 * K) * d3) * q by ring]
    rw [Nat.add_mul_div_left _ _ hfullStride, Nat.div_eq_of_lt hrem, Nat.zero_add]
  have hremEq : ((q * (d2 * K) + (r * d2 + p)) * d3 + j) %
      ((d2 * K) * d3) = (r * d2 + p) * d3 + j := by
    rw [show (q * (d2 * K) + (r * d2 + p)) * d3 + j =
        ((r * d2 + p) * d3 + j) + ((d2 * K) * d3) * q by ring]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem]
  have hjFull : ((r * d2 + p) * d3 + j) / d3 = r * d2 + p := by
    rw [show (r * d2 + p) * d3 + j = j + d3 * (r * d2 + p) by ring,
      Nat.add_mul_div_left j (r * d2 + p) hd3, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hk : ((r * d2 + p) * d3 + j) % d3 = j := by
    rw [show (r * d2 + p) * d3 + j = j + d3 * (r * d2 + p) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hrank : (r * d2 + p) / d2 = r := by
    rw [show r * d2 + p = p + d2 * r by ring,
      Nat.add_mul_div_left p r hd2, Nat.div_eq_of_lt hp, Nat.zero_add]
  have hpLocal : (r * d2 + p) % d2 = p := by
    rw [show r * d2 + p = p + d2 * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Nat.one_mul,
    if_neg (Nat.ne_of_gt hfullStride), if_neg (Nat.ne_of_gt hd3),
    if_neg (Nat.ne_of_gt hd2), hpre, hremEq, hjFull, hk, hrank, hpLocal]
  congr 1
  ring

/-- A canonical value read through a dim-1 gather of rank-4 shards. -/
theorem allGatherPrimDimN_dim1_rank4_valAt
    (xs : List Tensor) (K d0 d1 d2 d3 q r p u j : Nat)
    (hK : 0 < K) (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3)
    (hq : q < d0) (hr : r < K) (hp : p < d1) (hu : u < d2) (hj : j < d3)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0, d1, d2, d3]) :
    valAt (allGatherPrimDimN 1 K 0 xs)
        (((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + j) =
      valAt (xs.getD r (zeroTensor [d0, d1, d2, d3]))
        (((q * d1 + p) * d2 + u) * d3 + j) := by
  have hfullShape : (allGatherPrimDimN 1 K 0 xs).shape = [d0, d1 * K, d2, d3] := by
    rw [allGatherPrimDimN_shape 1 K xs [d0, d1, d2, d3] hhead]
    simp [List.set, List.getD]
  have hlocal : r * d1 + p < d1 * K := by
    have hstep : r * d1 + p < (r + 1) * d1 := by
      rw [Nat.add_mul]
      omega
    have hr1 : r + 1 ≤ K := by omega
    have hmul := Nat.mul_le_mul_right d1 hr1
    rw [Nat.mul_comm K d1] at hmul
    exact lt_of_lt_of_le hstep hmul
  have hmid : q * (d1 * K) + (r * d1 + p) < d0 * (d1 * K) := by
    have hstep : q * (d1 * K) + (r * d1 + p) < (q + 1) * (d1 * K) := by
      rw [Nat.add_mul]
      omega
    have hq1 : q + 1 ≤ d0 := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right (d1 * K) hq1)
  have hrow : (q * (d1 * K) + (r * d1 + p)) * d2 + u <
      d0 * (d1 * K) * d2 := by
    have hstep : (q * (d1 * K) + (r * d1 + p)) * d2 + u <
        (q * (d1 * K) + (r * d1 + p) + 1) * d2 := by
      calc
        _ < (q * (d1 * K) + (r * d1 + p)) * d2 + d2 :=
          Nat.add_lt_add_left hu _
        _ = _ := by ring
    have hmid1 : q * (d1 * K) + (r * d1 + p) + 1 ≤ d0 * (d1 * K) := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d2 hmid1)
  have hidx : ((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + j <
      d0 * (d1 * K) * d2 * d3 := by
    have hstep : ((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + j <
        ((q * (d1 * K) + (r * d1 + p)) * d2 + u + 1) * d3 := by
      calc
        _ < ((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + d3 :=
          Nat.add_lt_add_left hj _
        _ = _ := by ring
    have hrow1 : (q * (d1 * K) + (r * d1 + p)) * d2 + u + 1 ≤
        d0 * (d1 * K) * d2 := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d3 hrow1)
  have hidxProd : ((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + j <
      prodShape (allGatherPrimDimN 1 K 0 xs).shape := by
    rw [hfullShape]
    simpa [prodShape, Nat.mul_assoc] using hidx
  rw [valAt_of_lt _ _ hidxProd]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl]
  have hD1K : 0 < d1 * K := Nat.mul_pos hd1 hK
  have hpost : 0 < d2 * d3 := Nat.mul_pos hd2 hd3
  have hfullStride : 0 < (d1 * K) * (d2 * d3) := Nat.mul_pos hD1K hpost
  have htail : u * d3 + j < d2 * d3 := by
    have hstep : u * d3 + j < (u + 1) * d3 := by
      calc
        _ < u * d3 + d3 := Nat.add_lt_add_left hj _
        _ = _ := by ring
    have hu1 : u + 1 ≤ d2 := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d3 hu1)
  have hrem : (r * d1 + p) * (d2 * d3) + (u * d3 + j) <
      (d1 * K) * (d2 * d3) := by
    have hstep : (r * d1 + p) * (d2 * d3) + (u * d3 + j) <
        (r * d1 + p + 1) * (d2 * d3) := by
      calc
        _ < (r * d1 + p) * (d2 * d3) + (d2 * d3) :=
          Nat.add_lt_add_left htail _
        _ = _ := by ring
    have hlocal1 : r * d1 + p + 1 ≤ d1 * K := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right (d2 * d3) hlocal1)
  let idx := ((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + j
  have hcanon : idx = q * ((d1 * K) * (d2 * d3)) +
      ((r * d1 + p) * (d2 * d3) + (u * d3 + j)) := by
    dsimp [idx]
    ring
  have hpre : idx / ((d1 * K) * (d2 * d3)) = q := by
    rw [hcanon, show q * ((d1 * K) * (d2 * d3)) =
      ((d1 * K) * (d2 * d3)) * q by ring]
    rw [Nat.mul_add_div hfullStride, Nat.div_eq_of_lt hrem, Nat.add_zero]
  have hremEq : idx % ((d1 * K) * (d2 * d3)) =
      (r * d1 + p) * (d2 * d3) + (u * d3 + j) := by
    rw [hcanon, show q * ((d1 * K) * (d2 * d3)) =
      ((d1 * K) * (d2 * d3)) * q by ring]
    rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrem]
  have hjFull : ((r * d1 + p) * (d2 * d3) + (u * d3 + j)) /
      (d2 * d3) = r * d1 + p := by
    rw [show (r * d1 + p) * (d2 * d3) + (u * d3 + j) =
        (u * d3 + j) + (d2 * d3) * (r * d1 + p) by ring,
      Nat.add_mul_div_left _ _ hpost, Nat.div_eq_of_lt htail, Nat.zero_add]
  have hk : ((r * d1 + p) * (d2 * d3) + (u * d3 + j)) %
      (d2 * d3) = u * d3 + j := by
    rw [show (r * d1 + p) * (d2 * d3) + (u * d3 + j) =
        (u * d3 + j) + (d2 * d3) * (r * d1 + p) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htail]
  have hrank : (r * d1 + p) / d1 = r := by
    rw [show r * d1 + p = p + d1 * r by ring,
      Nat.add_mul_div_left p r hd1, Nat.div_eq_of_lt hp, Nat.zero_add]
  have hpLocal : (r * d1 + p) % d1 = p := by
    rw [show r * d1 + p = p + d1 * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  have hpick : idx % ((d1 * K) * (d2 * d3)) / (d2 * d3) / d1 = r := by
    rw [hremEq, hjFull, hrank]
  have hflat :
      idx / ((d1 * K) * (d2 * d3)) * (d1 * (d2 * d3)) +
          idx % ((d1 * K) * (d2 * d3)) / (d2 * d3) % d1 * (d2 * d3) +
        idx % ((d1 * K) * (d2 * d3)) % (d2 * d3) =
      ((q * d1 + p) * d2 + u) * d3 + j := by
    rw [hpre, hremEq, hjFull, hpLocal, hk]
    ring
  dsimp [idx] at hpick hflat
  change valAt (xs.getD _ _) _ = _
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Nat.one_mul,
    if_neg (Nat.ne_of_gt hfullStride), if_neg (Nat.ne_of_gt hpost),
    if_neg (Nat.ne_of_gt hd1)]
  rw [hpick, hflat]

-- Last-axis softmax commutes with an arbitrary nonempty ordered dim-2 gather
-- of rank-4 shards.  Only the last extent must be positive.
set_option maxHeartbeats 3200000 in
theorem fw_softmax_allGatherPrimDimN_dim2_rank4
    (xs : List Tensor) (d0 d1 d2 d3 : Nat)
    (hne : xs ≠ []) (hd3 : 0 < d3)
    (hshapes : ∀ x ∈ xs, x.shape = [d0, d1, d2, d3]) :
    fw_softmax (allGatherPrimDimN 2 xs.length 0 xs) =
      allGatherPrimDimN 2 xs.length 0 (xs.map fw_softmax) := by
  have hK : 0 < xs.length := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons x rest => simp
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0, d1, d2, d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  have hmapHead : (((xs.map fw_softmax).head?.map (fun t => t.shape)).getD []) =
      [d0, d1, d2, d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest =>
      simp only [List.map, List.head?, Option.map, Option.getD]
      rw [fw_softmax_shape_g43, hshapes x (by simp)]
  have hfullShape : (allGatherPrimDimN 2 xs.length 0 xs).shape =
      [d0, d1, d2 * xs.length, d3] := by
    rw [allGatherPrimDimN_shape 2 xs.length xs [d0, d1, d2, d3] hhead]
    simp [List.set, List.getD]
  have hlhsShape : (fw_softmax (allGatherPrimDimN 2 xs.length 0 xs)).shape =
      [d0, d1, d2 * xs.length, d3] := by
    rw [fw_softmax_shape_g43, hfullShape]
  have hrhsShape : (allGatherPrimDimN 2 xs.length 0 (xs.map fw_softmax)).shape =
      [d0, d1, d2 * xs.length, d3] := by
    rw [allGatherPrimDimN_shape 2 xs.length _ [d0, d1, d2, d3] hmapHead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhsShape, hrhsShape])
  intro idx hidx
  have hbound : idx < (d0 * d1) * (d2 * xs.length) * d3 := by
    rw [hlhsShape] at hidx
    simpa [prodShape, Nat.mul_assoc] using hidx
  by_cases hd2z : d2 = 0
  · subst d2
    simp at hbound
  have hd2 : 0 < d2 := Nat.pos_of_ne_zero hd2z
  set j := idx % d3 with hjDef
  set row := idx / d3 with hrowDef
  have hj : j < d3 := by rw [hjDef]; exact Nat.mod_lt _ hd3
  have hrow : row < (d0 * d1) * (d2 * xs.length) := by
    rw [hrowDef, Nat.div_lt_iff_lt_mul hd3]
    simpa [Nat.mul_assoc] using hbound
  set q := row / (d2 * xs.length) with hqDef
  set g := row % (d2 * xs.length) with hgDef
  have hDK : 0 < d2 * xs.length := Nat.mul_pos hd2 hK
  have hq : q < d0 * d1 := by
    rw [hqDef, Nat.div_lt_iff_lt_mul hDK]
    exact hrow
  have hg : g < d2 * xs.length := by rw [hgDef]; exact Nat.mod_lt _ hDK
  set r := g / d2 with hrDef
  set p := g % d2 with hpDef
  have hr : r < xs.length := by
    rw [hrDef, Nat.div_lt_iff_lt_mul hd2]
    simpa [Nat.mul_comm] using hg
  have hp : p < d2 := by rw [hpDef]; exact Nat.mod_lt _ hd2
  have hrowEq : row = q * (d2 * xs.length) + (r * d2 + p) := by
    have h1 := (Nat.div_add_mod row (d2 * xs.length)).symm
    have h2 := (Nat.div_add_mod g d2).symm
    rw [← hqDef, ← hgDef] at h1
    rw [← hrDef, ← hpDef] at h2
    calc
      row = d2 * xs.length * q + g := h1
      _ = q * (d2 * xs.length) + g := by ring
      _ = q * (d2 * xs.length) + (r * d2 + p) := by rw [h2]; ring
  have hidxEq : idx = (q * (d2 * xs.length) + (r * d2 + p)) * d3 + j := by
    have h := (Nat.div_add_mod idx d3).symm
    rw [← hrowDef, ← hjDef] at h
    calc
      idx = d3 * row + j := h
      _ = row * d3 + j := by ring
      _ = _ := by rw [hrowEq]
  have hboundCanonical :
      (q * (d2 * xs.length) + (r * d2 + p)) * d3 + j <
        (d0 * d1) * (d2 * xs.length) * d3 := by
    rw [← hidxEq]
    exact hbound
  rw [hidxEq]
  have hxr : (xs.getD r (zeroTensor [d0, d1, d2, d3])).shape =
      [d0, d1, d2, d3] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
    simpa using hshapes xs[r] (List.getElem_mem hr)
  have hlocalRow : q * d2 + p < (d0 * d1) * d2 := by
    have hstep : q * d2 + p < (q + 1) * d2 := by
      rw [Nat.add_mul]
      omega
    have hq1 : q + 1 ≤ d0 * d1 := by omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d2 hq1)
  have hlocal : (q * d2 + p) * d3 + j < (d0 * d1) * d2 * d3 := by
    have hstep : (q * d2 + p) * d3 + j < (q * d2 + p + 1) * d3 := by
      calc
        _ < (q * d2 + p) * d3 + d3 := Nat.add_lt_add_left hj _
        _ = _ := by ring
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d3 (by omega))
  have hmapGet : (xs.map fw_softmax).getD r (zeroTensor [d0, d1, d2, d3]) =
      fw_softmax (xs.getD r (zeroTensor [d0, d1, d2, d3])) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hr, Option.map_some, Option.getD_some]
  rw [fw_softmax_valAt_g43 (allGatherPrimDimN 2 xs.length 0 xs) d3
      [d2 * xs.length, d1, d0] (by rw [hfullShape]; rfl) (Nat.ne_of_gt hd3)
      _ (by rw [hfullShape]; simpa [prodShape, Nat.mul_assoc] using hboundCanonical)]
  rw [allGatherPrimDimN_dim2_rank4_valAt (xs.map fw_softmax) xs.length
      d0 d1 d2 d3 q r p j hK hd2 hd3 hq hr hp hj hmapHead, hmapGet]
  rw [fw_softmax_valAt_g43 (xs.getD r (zeroTensor [d0, d1, d2, d3])) d3
      [d2, d1, d0] (by rw [hxr]; rfl) (Nat.ne_of_gt hd3)
      _ (by rw [hxr]; simpa [prodShape, Nat.mul_assoc] using hlocal)]
  have hglobalDiv : ((q * (d2 * xs.length) + (r * d2 + p)) * d3 + j) / d3 =
      q * (d2 * xs.length) + (r * d2 + p) := by
    rw [show (q * (d2 * xs.length) + (r * d2 + p)) * d3 + j =
      j + d3 * (q * (d2 * xs.length) + (r * d2 + p)) by ring,
      Nat.add_mul_div_left _ _ hd3, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hlocalDiv : ((q * d2 + p) * d3 + j) / d3 = q * d2 + p := by
    rw [show (q * d2 + p) * d3 + j = j + d3 * (q * d2 + p) by ring,
      Nat.add_mul_div_left _ _ hd3, Nat.div_eq_of_lt hj, Nat.zero_add]
  rw [hglobalDiv, hlocalDiv]
  have hsum :
      (∑ z ∈ Finset.range d3,
        expFn (valAt (allGatherPrimDimN 2 xs.length 0 xs)
          ((q * (d2 * xs.length) + (r * d2 + p)) * d3 + z))) =
      ∑ z ∈ Finset.range d3,
        expFn (valAt (xs.getD r (zeroTensor [d0, d1, d2, d3]))
          ((q * d2 + p) * d3 + z)) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.mem_range] at hz
    rw [allGatherPrimDimN_dim2_rank4_valAt xs xs.length d0 d1 d2 d3 q r p z
      hK hd2 hd3 hq hr hp hz hhead]
  rw [hsum]
  rw [allGatherPrimDimN_dim2_rank4_valAt xs xs.length d0 d1 d2 d3 q r p j
    hK hd2 hd3 hq hr hp hj hhead]

-- Last-axis softmax commutes with an arbitrary nonempty ordered dim-1 gather
-- of rank-4 shards.  Only the last extent must be positive.
set_option maxHeartbeats 3200000 in
theorem fw_softmax_allGatherPrimDimN_dim1_rank4
    (xs : List Tensor) (d0 d1 d2 d3 : Nat)
    (hne : xs ≠ []) (hd3 : 0 < d3)
    (hshapes : ∀ x ∈ xs, x.shape = [d0, d1, d2, d3]) :
    fw_softmax (allGatherPrimDimN 1 xs.length 0 xs) =
      allGatherPrimDimN 1 xs.length 0 (xs.map fw_softmax) := by
  have hK : 0 < xs.length := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons x rest => simp
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0, d1, d2, d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  have hmapHead : (((xs.map fw_softmax).head?.map (fun t => t.shape)).getD []) =
      [d0, d1, d2, d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest =>
      simp only [List.map, List.head?, Option.map, Option.getD]
      rw [fw_softmax_shape_g43, hshapes x (by simp)]
  have hfullShape : (allGatherPrimDimN 1 xs.length 0 xs).shape =
      [d0, d1 * xs.length, d2, d3] := by
    rw [allGatherPrimDimN_shape 1 xs.length xs [d0, d1, d2, d3] hhead]
    simp [List.set, List.getD]
  have hlhsShape : (fw_softmax (allGatherPrimDimN 1 xs.length 0 xs)).shape =
      [d0, d1 * xs.length, d2, d3] := by
    rw [fw_softmax_shape_g43, hfullShape]
  have hrhsShape : (allGatherPrimDimN 1 xs.length 0 (xs.map fw_softmax)).shape =
      [d0, d1 * xs.length, d2, d3] := by
    rw [allGatherPrimDimN_shape 1 xs.length _ [d0, d1, d2, d3] hmapHead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhsShape, hrhsShape])
  intro idx hidx
  have hbound : idx < d0 * (d1 * xs.length) * d2 * d3 := by
    rw [hlhsShape] at hidx
    simpa [prodShape, Nat.mul_assoc] using hidx
  by_cases hd1z : d1 = 0
  · subst d1
    simp at hbound
  by_cases hd2z : d2 = 0
  · subst d2
    simp at hbound
  have hd1 : 0 < d1 := Nat.pos_of_ne_zero hd1z
  have hd2 : 0 < d2 := Nat.pos_of_ne_zero hd2z
  set j := idx % d3 with hjDef
  set row := idx / d3 with hrowDef
  have hj : j < d3 := by rw [hjDef]; exact Nat.mod_lt _ hd3
  have hrow : row < d0 * (d1 * xs.length) * d2 := by
    rw [hrowDef, Nat.div_lt_iff_lt_mul hd3]
    simpa [Nat.mul_assoc] using hbound
  set u := row % d2 with huDef
  set mid := row / d2 with hmidDef
  have hu : u < d2 := by rw [huDef]; exact Nat.mod_lt _ hd2
  have hmid : mid < d0 * (d1 * xs.length) := by
    rw [hmidDef, Nat.div_lt_iff_lt_mul hd2]
    exact hrow
  set q := mid / (d1 * xs.length) with hqDef
  set g := mid % (d1 * xs.length) with hgDef
  have hDK : 0 < d1 * xs.length := Nat.mul_pos hd1 hK
  have hq : q < d0 := by
    rw [hqDef, Nat.div_lt_iff_lt_mul hDK]
    exact hmid
  have hg : g < d1 * xs.length := by rw [hgDef]; exact Nat.mod_lt _ hDK
  set r := g / d1 with hrDef
  set p := g % d1 with hpDef
  have hr : r < xs.length := by
    rw [hrDef, Nat.div_lt_iff_lt_mul hd1]
    simpa [Nat.mul_comm] using hg
  have hp : p < d1 := by rw [hpDef]; exact Nat.mod_lt _ hd1
  have hmidEq : mid = q * (d1 * xs.length) + (r * d1 + p) := by
    have h1 := (Nat.div_add_mod mid (d1 * xs.length)).symm
    have h2 := (Nat.div_add_mod g d1).symm
    rw [← hqDef, ← hgDef] at h1
    rw [← hrDef, ← hpDef] at h2
    calc
      mid = d1 * xs.length * q + g := h1
      _ = q * (d1 * xs.length) + g := by ring
      _ = q * (d1 * xs.length) + (r * d1 + p) := by rw [h2]; ring
  have hrowEq : row = (q * (d1 * xs.length) + (r * d1 + p)) * d2 + u := by
    have h := (Nat.div_add_mod row d2).symm
    rw [← hmidDef, ← huDef] at h
    calc
      row = d2 * mid + u := h
      _ = mid * d2 + u := by ring
      _ = _ := by rw [hmidEq]
  have hidxEq : idx =
      ((q * (d1 * xs.length) + (r * d1 + p)) * d2 + u) * d3 + j := by
    have h := (Nat.div_add_mod idx d3).symm
    rw [← hrowDef, ← hjDef] at h
    calc
      idx = d3 * row + j := h
      _ = row * d3 + j := by ring
      _ = _ := by rw [hrowEq]
  have hboundCanonical :
      ((q * (d1 * xs.length) + (r * d1 + p)) * d2 + u) * d3 + j <
        d0 * (d1 * xs.length) * d2 * d3 := by
    rw [← hidxEq]
    exact hbound
  rw [hidxEq]
  have hxr : (xs.getD r (zeroTensor [d0, d1, d2, d3])).shape =
      [d0, d1, d2, d3] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
    simpa using hshapes xs[r] (List.getElem_mem hr)
  have hlocalMid : q * d1 + p < d0 * d1 := by
    have hstep : q * d1 + p < (q + 1) * d1 := by
      rw [Nat.add_mul]
      omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d1 (by omega))
  have hlocalRow : (q * d1 + p) * d2 + u < d0 * d1 * d2 := by
    have hstep : (q * d1 + p) * d2 + u < (q * d1 + p + 1) * d2 := by
      calc
        _ < (q * d1 + p) * d2 + d2 := Nat.add_lt_add_left hu _
        _ = _ := by ring
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d2 (by omega))
  have hlocal : ((q * d1 + p) * d2 + u) * d3 + j < d0 * d1 * d2 * d3 := by
    have hstep : ((q * d1 + p) * d2 + u) * d3 + j <
        ((q * d1 + p) * d2 + u + 1) * d3 := by
      calc
        _ < ((q * d1 + p) * d2 + u) * d3 + d3 := Nat.add_lt_add_left hj _
        _ = _ := by ring
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d3 (by omega))
  have hmapGet : (xs.map fw_softmax).getD r (zeroTensor [d0, d1, d2, d3]) =
      fw_softmax (xs.getD r (zeroTensor [d0, d1, d2, d3])) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hr, Option.map_some, Option.getD_some]
  rw [fw_softmax_valAt_g43 (allGatherPrimDimN 1 xs.length 0 xs) d3
      [d2, d1 * xs.length, d0] (by rw [hfullShape]; rfl) (Nat.ne_of_gt hd3)
      _ (by rw [hfullShape]; simpa [prodShape, Nat.mul_assoc] using hboundCanonical)]
  rw [allGatherPrimDimN_dim1_rank4_valAt (xs.map fw_softmax) xs.length
      d0 d1 d2 d3 q r p u j hK hd1 hd2 hd3 hq hr hp hu hj hmapHead, hmapGet]
  rw [fw_softmax_valAt_g43 (xs.getD r (zeroTensor [d0, d1, d2, d3])) d3
      [d2, d1, d0] (by rw [hxr]; rfl) (Nat.ne_of_gt hd3)
      _ (by rw [hxr]; simpa [prodShape, Nat.mul_assoc] using hlocal)]
  have hglobalDiv :
      (((q * (d1 * xs.length) + (r * d1 + p)) * d2 + u) * d3 + j) / d3 =
        (q * (d1 * xs.length) + (r * d1 + p)) * d2 + u := by
    rw [show (((q * (d1 * xs.length) + (r * d1 + p)) * d2 + u) * d3 + j) =
      j + d3 * ((q * (d1 * xs.length) + (r * d1 + p)) * d2 + u) by ring,
      Nat.add_mul_div_left _ _ hd3, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hlocalDiv : (((q * d1 + p) * d2 + u) * d3 + j) / d3 =
      (q * d1 + p) * d2 + u := by
    rw [show (((q * d1 + p) * d2 + u) * d3 + j) =
      j + d3 * ((q * d1 + p) * d2 + u) by ring,
      Nat.add_mul_div_left _ _ hd3, Nat.div_eq_of_lt hj, Nat.zero_add]
  rw [hglobalDiv, hlocalDiv]
  have hsum :
      (∑ z ∈ Finset.range d3,
        expFn (valAt (allGatherPrimDimN 1 xs.length 0 xs)
          (((q * (d1 * xs.length) + (r * d1 + p)) * d2 + u) * d3 + z))) =
      ∑ z ∈ Finset.range d3,
        expFn (valAt (xs.getD r (zeroTensor [d0, d1, d2, d3]))
          (((q * d1 + p) * d2 + u) * d3 + z)) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.mem_range] at hz
    rw [allGatherPrimDimN_dim1_rank4_valAt xs xs.length d0 d1 d2 d3 q r p u z
      hK hd1 hd2 hd3 hq hr hp hu hz hhead]
  rw [hsum]
  rw [allGatherPrimDimN_dim1_rank4_valAt xs xs.length d0 d1 d2 d3 q r p u j
    hK hd1 hd2 hd3 hq hr hp hu hj hhead]

end

end TrainVerify.Denote

namespace TrainVerify.Denote.RelationCompiler

noncomputable section

/-- Exact rank-4 dim-1 sharding transport for last-axis `FW_softmax`. -/
theorem ShardedRel.fw_softmax_dim1_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : ShardedRel full shards 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3])
    (hd3 : 0 < d3) :
    ShardedRel (fw_softmax full) (shards.map fw_softmax) 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      fw_softmax_allGatherPrimDimN_dim1_rank4 shards d0 d1 d2 d3
        h.shards_nonempty hd3 h.shard_shapes
  · rw [fw_softmax_shape_g43, h.full_shape]
  · simpa using h.shards_nonempty
  · exact h.gather_dim_lt
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    rw [fw_softmax_shape_g43, h.shard_shapes source hsource]
  · simpa only [List.length_map] using h.shape_contract

/-- Exact rank-4 dim-2 sharding transport for last-axis `FW_softmax`. -/
theorem ShardedRel.fw_softmax_dim2_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : ShardedRel full shards 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3])
    (hd3 : 0 < d3) :
    ShardedRel (fw_softmax full) (shards.map fw_softmax) 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      fw_softmax_allGatherPrimDimN_dim2_rank4 shards d0 d1 d2 d3
        h.shards_nonempty hd3 h.shard_shapes
  · rw [fw_softmax_shape_g43, h.full_shape]
  · simpa using h.shards_nonempty
  · exact h.gather_dim_lt
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    rw [fw_softmax_shape_g43, h.shard_shapes source hsource]
  · simpa only [List.length_map] using h.shape_contract

end

end TrainVerify.Denote.RelationCompiler
