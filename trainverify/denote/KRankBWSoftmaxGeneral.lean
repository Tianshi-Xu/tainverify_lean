import denote.KRankSoftmaxGather

namespace TrainVerify.Denote

noncomputable section
open scoped BigOperators

/-!
任意正 K、四维分片及 axis = 1 或 2 的真实 BW_softmax gather 交换律。
先证明 softmaxBwdFromOutput 的逐行导数交换律，再复用 FW_softmax 交换律，
在顶层严格保留 bw_softmax g x = softmaxBwdFromOutput g (softmax x) 的输入语义。
-/

private theorem bwsg_head (ts : List Tensor) (K : Nat) (sh : Shape)
    (hK : 0 < K) (hlen : ts.length = K)
    (hsh : ∀ t ∈ ts, t.shape = sh) :
    (ts.head?.map (fun t => t.shape)).getD [] = sh := by
  have h0 : 0 < ts.length := by omega
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
  simp only [Option.map_some, Option.getD_some]
  exact hsh ts[0] (List.getElem_mem h0)

private theorem bwsg_get_shape (ts : List Tensor) (K r : Nat) (sh : Shape)
    (hlen : ts.length = K) (hr : r < K)
    (hsh : ∀ t ∈ ts, t.shape = sh) :
    (ts.getD r (zeroTensor sh)).shape = sh := by
  have hrt : r < ts.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrt]
  exact hsh ts[r] (List.getElem_mem hrt)

private theorem bwsg_zip_get (f : Tensor → Tensor → Tensor)
    (gs xs : List Tensor) (K r : Nat) (sh : Shape)
    (hg : gs.length = K) (hx : xs.length = K) (hr : r < K) :
    (List.zipWith f gs xs).getD r (zeroTensor sh) =
      f (gs.getD r (zeroTensor sh)) (xs.getD r (zeroTensor sh)) := by
  have hrg : r < gs.length := by omega
  have hrx : r < xs.length := by omega
  have hrz : r < (List.zipWith f gs xs).length := by
    rw [List.length_zipWith, hg, hx, Nat.min_self]
    exact hr
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrz,
    List.getElem?_eq_getElem hrg, List.getElem?_eq_getElem hrx, Option.getD_some]
  exact List.getElem_zipWith

private theorem bwsg_pure_shape (g y : Tensor) (a b c d : Nat)
    (hy : y.shape = [a, b, c, d]) :
    (softmaxBwdFromOutput g y).shape = [a, b, c, d] := by
  have hrev : y.shape.reverse = d :: [c, b, a] := by rw [hy]; rfl
  unfold softmaxBwdFromOutput
  rw [hrev]
  exact hy

-- The only analytic step: a full row is read, including every derivative-dot summand.
private theorem bwsg_pure_row (g y : Tensor) (d row j : Nat) (rest : List Nat)
    (hy : y.shape.reverse = d :: rest) (hd : 0 < d) (hj : j < d)
    (hi : row * d + j < prodShape y.shape) :
    valAt (softmaxBwdFromOutput g y) (row * d + j) =
      valAt y (row * d + j) *
        (valAt g (row * d + j) -
          ∑ z ∈ Finset.range d, valAt y (row * d + z) * valAt g (row * d + z)) := by
  unfold softmaxBwdFromOutput
  rw [hy]
  rw [valAt_of_lt _ _ (by exact hi)]
  simp only [Tensor.mkShape, if_neg (Nat.ne_of_gt hd)]
  have hdiv : (row * d + j) / d = row := by
    rw [show row * d + j = j + d * row by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (row * d + j) % d = j := by
    rw [show row * d + j = j + d * row by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [hdiv, hmod]

set_option maxHeartbeats 3200000 in
private theorem bwsg_pure_dim2
    (gs xs : List Tensor) (K d0 d1 d2 d3 : Nat)
    (hK : 0 < K) (hd3 : 0 < d3)
    (hleng : gs.length = K) (hlenx : xs.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [d0, d1, d2, d3])
    (hxs : ∀ x ∈ xs, x.shape = [d0, d1, d2, d3]) :
    softmaxBwdFromOutput (allGatherPrimDimN 2 K 0 gs)
        (allGatherPrimDimN 2 K 0 xs) =
      allGatherPrimDimN 2 K 0 (List.zipWith softmaxBwdFromOutput gs xs) := by
  have hhead := bwsg_head xs K [d0, d1, d2, d3] hK hlenx hxs
  have hghead := bwsg_head gs K [d0, d1, d2, d3] hK hleng hgs
  have hziplen : (List.zipWith softmaxBwdFromOutput gs xs).length = K := by
    rw [List.length_zipWith, hleng, hlenx, Nat.min_self]
  have hziphead :
      ((List.zipWith softmaxBwdFromOutput gs xs).head?.map (fun t => t.shape)).getD [] =
        [d0, d1, d2, d3] := by
    have h0 : 0 < (List.zipWith softmaxBwdFromOutput gs xs).length := by omega
    have hx0 : 0 < xs.length := by omega
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
    simp only [Option.map_some, Option.getD_some]
    rw [List.getElem_zipWith]
    exact bwsg_pure_shape _ _ d0 d1 d2 d3 (hxs xs[0] (List.getElem_mem hx0))
  have hfullShape : (allGatherPrimDimN 2 K 0 xs).shape = [d0, d1, d2 * K, d3] := by
    rw [allGatherPrimDimN_shape 2 K xs [d0, d1, d2, d3] hhead]
    simp [List.set, List.getD]
  have hlhsShape :
      (softmaxBwdFromOutput (allGatherPrimDimN 2 K 0 gs)
        (allGatherPrimDimN 2 K 0 xs)).shape = [d0, d1, d2 * K, d3] :=
    bwsg_pure_shape _ _ d0 d1 (d2 * K) d3 hfullShape
  have hrhsShape :
      (allGatherPrimDimN 2 K 0 (List.zipWith softmaxBwdFromOutput gs xs)).shape =
        [d0, d1, d2 * K, d3] := by
    rw [allGatherPrimDimN_shape 2 K _ [d0, d1, d2, d3] hziphead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhsShape, hrhsShape])
  intro idx hidx
  have hbound : idx < (d0 * d1) * (d2 * K) * d3 := by
    rw [hlhsShape] at hidx
    simpa [prodShape, Nat.mul_assoc] using hidx
  by_cases hd2z : d2 = 0
  · subst d2
    simp at hbound
  have hd2 : 0 < d2 := Nat.pos_of_ne_zero hd2z
  set j := idx % d3 with hjDef
  set row := idx / d3 with hrowDef
  have hj : j < d3 := by rw [hjDef]; exact Nat.mod_lt _ hd3
  have hrow : row < (d0 * d1) * (d2 * K) := by
    rw [hrowDef, Nat.div_lt_iff_lt_mul hd3]
    simpa [Nat.mul_assoc] using hbound
  set q := row / (d2 * K) with hqDef
  set g := row % (d2 * K) with hgDef
  have hDK : 0 < d2 * K := Nat.mul_pos hd2 hK
  have hq : q < d0 * d1 := by
    rw [hqDef, Nat.div_lt_iff_lt_mul hDK]
    exact hrow
  have hg : g < d2 * K := by rw [hgDef]; exact Nat.mod_lt _ hDK
  set r := g / d2 with hrDef
  set p := g % d2 with hpDef
  have hr : r < K := by
    rw [hrDef, Nat.div_lt_iff_lt_mul hd2]
    simpa [Nat.mul_comm] using hg
  have hp : p < d2 := by rw [hpDef]; exact Nat.mod_lt _ hd2
  have hrowEq : row = q * (d2 * K) + (r * d2 + p) := by
    have h1 := (Nat.div_add_mod row (d2 * K)).symm
    have h2 := (Nat.div_add_mod g d2).symm
    rw [← hqDef, ← hgDef] at h1
    rw [← hrDef, ← hpDef] at h2
    calc
      row = d2 * K * q + g := h1
      _ = q * (d2 * K) + g := by ring
      _ = q * (d2 * K) + (r * d2 + p) := by rw [h2]; ring
  have hidxEq : idx = (q * (d2 * K) + (r * d2 + p)) * d3 + j := by
    have h := (Nat.div_add_mod idx d3).symm
    rw [← hrowDef, ← hjDef] at h
    calc
      idx = d3 * row + j := h
      _ = row * d3 + j := by ring
      _ = _ := by rw [hrowEq]
  have hboundCanonical :
      (q * (d2 * K) + (r * d2 + p)) * d3 + j <
        (d0 * d1) * (d2 * K) * d3 := by
    rw [← hidxEq]
    exact hbound
  rw [hidxEq]
  have hxr : (xs.getD r (zeroTensor [d0, d1, d2, d3])).shape =
      [d0, d1, d2, d3] :=
    bwsg_get_shape xs K r [d0, d1, d2, d3] hlenx hr hxs
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
  rw [allGatherPrimDimN_dim2_rank4_valAt
    (List.zipWith softmaxBwdFromOutput gs xs) K d0 d1 d2 d3 q r p j
    hK hd2 hd3 hq hr hp hj hziphead]
  rw [bwsg_zip_get softmaxBwdFromOutput gs xs K r [d0, d1, d2, d3]
    hleng hlenx hr]
  rw [bwsg_pure_row (allGatherPrimDimN 2 K 0 gs)
    (allGatherPrimDimN 2 K 0 xs) d3 (q * (d2 * K) + (r * d2 + p)) j [d2 * K, d1, d0]
    (by rw [hfullShape]; rfl) hd3 hj
    (by rw [hfullShape]; simpa [prodShape, Nat.mul_assoc] using hboundCanonical)]
  rw [bwsg_pure_row (gs.getD r (zeroTensor [d0, d1, d2, d3]))
    (xs.getD r (zeroTensor [d0, d1, d2, d3])) d3 (q * d2 + p) j [d2, d1, d0]
    (by rw [hxr]; rfl) hd3 hj
    (by rw [hxr]; simpa [prodShape, Nat.mul_assoc] using hlocal)]
  have hsum :
      (∑ z ∈ Finset.range d3,
        valAt (allGatherPrimDimN 2 K 0 xs) ((q * (d2 * K) + (r * d2 + p)) * d3 + z) *
          valAt (allGatherPrimDimN 2 K 0 gs) ((q * (d2 * K) + (r * d2 + p)) * d3 + z)) =
      ∑ z ∈ Finset.range d3,
        valAt (xs.getD r (zeroTensor [d0, d1, d2, d3])) ((q * d2 + p) * d3 + z) *
          valAt (gs.getD r (zeroTensor [d0, d1, d2, d3])) ((q * d2 + p) * d3 + z) := by
    apply Finset.sum_congr rfl
    intro z hz
    have hz' := Finset.mem_range.mp hz
    rw [allGatherPrimDimN_dim2_rank4_valAt xs K d0 d1 d2 d3 q r p z
      hK hd2 hd3 hq hr hp hz' hhead,
      allGatherPrimDimN_dim2_rank4_valAt gs K d0 d1 d2 d3 q r p z
      hK hd2 hd3 hq hr hp hz' hghead]
  rw [hsum,
    allGatherPrimDimN_dim2_rank4_valAt xs K d0 d1 d2 d3 q r p j
      hK hd2 hd3 hq hr hp hj hhead,
    allGatherPrimDimN_dim2_rank4_valAt gs K d0 d1 d2 d3 q r p j
      hK hd2 hd3 hq hr hp hj hghead]

set_option maxHeartbeats 3200000 in
private theorem bwsg_pure_dim1
    (gs xs : List Tensor) (K d0 d1 d2 d3 : Nat)
    (hK : 0 < K) (hd3 : 0 < d3)
    (hleng : gs.length = K) (hlenx : xs.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [d0, d1, d2, d3])
    (hxs : ∀ x ∈ xs, x.shape = [d0, d1, d2, d3]) :
    softmaxBwdFromOutput (allGatherPrimDimN 1 K 0 gs)
        (allGatherPrimDimN 1 K 0 xs) =
      allGatherPrimDimN 1 K 0 (List.zipWith softmaxBwdFromOutput gs xs) := by
  have hhead := bwsg_head xs K [d0, d1, d2, d3] hK hlenx hxs
  have hghead := bwsg_head gs K [d0, d1, d2, d3] hK hleng hgs
  have hziplen : (List.zipWith softmaxBwdFromOutput gs xs).length = K := by
    rw [List.length_zipWith, hleng, hlenx, Nat.min_self]
  have hziphead :
      ((List.zipWith softmaxBwdFromOutput gs xs).head?.map (fun t => t.shape)).getD [] =
        [d0, d1, d2, d3] := by
    have h0 : 0 < (List.zipWith softmaxBwdFromOutput gs xs).length := by omega
    have hx0 : 0 < xs.length := by omega
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
    simp only [Option.map_some, Option.getD_some]
    rw [List.getElem_zipWith]
    exact bwsg_pure_shape _ _ d0 d1 d2 d3 (hxs xs[0] (List.getElem_mem hx0))
  have hfullShape : (allGatherPrimDimN 1 K 0 xs).shape = [d0, d1 * K, d2, d3] := by
    rw [allGatherPrimDimN_shape 1 K xs [d0, d1, d2, d3] hhead]
    simp [List.set, List.getD]
  have hlhsShape :
      (softmaxBwdFromOutput (allGatherPrimDimN 1 K 0 gs)
        (allGatherPrimDimN 1 K 0 xs)).shape = [d0, d1 * K, d2, d3] :=
    bwsg_pure_shape _ _ d0 (d1 * K) d2 d3 hfullShape
  have hrhsShape :
      (allGatherPrimDimN 1 K 0 (List.zipWith softmaxBwdFromOutput gs xs)).shape =
        [d0, d1 * K, d2, d3] := by
    rw [allGatherPrimDimN_shape 1 K _ [d0, d1, d2, d3] hziphead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhsShape, hrhsShape])
  intro idx hidx
  have hbound : idx < d0 * (d1 * K) * d2 * d3 := by
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
  have hrow : row < d0 * (d1 * K) * d2 := by
    rw [hrowDef, Nat.div_lt_iff_lt_mul hd3]
    simpa [Nat.mul_assoc] using hbound
  set u := row % d2 with huDef
  set mid := row / d2 with hmidDef
  have hu : u < d2 := by rw [huDef]; exact Nat.mod_lt _ hd2
  have hmid : mid < d0 * (d1 * K) := by
    rw [hmidDef, Nat.div_lt_iff_lt_mul hd2]
    exact hrow
  set q := mid / (d1 * K) with hqDef
  set g := mid % (d1 * K) with hgDef
  have hDK : 0 < d1 * K := Nat.mul_pos hd1 hK
  have hq : q < d0 := by
    rw [hqDef, Nat.div_lt_iff_lt_mul hDK]
    exact hmid
  have hg : g < d1 * K := by rw [hgDef]; exact Nat.mod_lt _ hDK
  set r := g / d1 with hrDef
  set p := g % d1 with hpDef
  have hr : r < K := by
    rw [hrDef, Nat.div_lt_iff_lt_mul hd1]
    simpa [Nat.mul_comm] using hg
  have hp : p < d1 := by rw [hpDef]; exact Nat.mod_lt _ hd1
  have hmidEq : mid = q * (d1 * K) + (r * d1 + p) := by
    have h1 := (Nat.div_add_mod mid (d1 * K)).symm
    have h2 := (Nat.div_add_mod g d1).symm
    rw [← hqDef, ← hgDef] at h1
    rw [← hrDef, ← hpDef] at h2
    calc
      mid = d1 * K * q + g := h1
      _ = q * (d1 * K) + g := by ring
      _ = q * (d1 * K) + (r * d1 + p) := by rw [h2]; ring
  have hrowEq : row = (q * (d1 * K) + (r * d1 + p)) * d2 + u := by
    have h := (Nat.div_add_mod row d2).symm
    rw [← hmidDef, ← huDef] at h
    calc
      row = d2 * mid + u := h
      _ = mid * d2 + u := by ring
      _ = _ := by rw [hmidEq]
  have hidxEq : idx =
      ((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + j := by
    have h := (Nat.div_add_mod idx d3).symm
    rw [← hrowDef, ← hjDef] at h
    calc
      idx = d3 * row + j := h
      _ = row * d3 + j := by ring
      _ = _ := by rw [hrowEq]
  have hboundCanonical :
      ((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + j <
        d0 * (d1 * K) * d2 * d3 := by
    rw [← hidxEq]
    exact hbound
  rw [hidxEq]
  have hxr : (xs.getD r (zeroTensor [d0, d1, d2, d3])).shape =
      [d0, d1, d2, d3] :=
    bwsg_get_shape xs K r [d0, d1, d2, d3] hlenx hr hxs
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
  rw [allGatherPrimDimN_dim1_rank4_valAt
    (List.zipWith softmaxBwdFromOutput gs xs) K d0 d1 d2 d3 q r p u j
    hK hd1 hd2 hd3 hq hr hp hu hj hziphead]
  rw [bwsg_zip_get softmaxBwdFromOutput gs xs K r [d0, d1, d2, d3]
    hleng hlenx hr]
  rw [bwsg_pure_row (allGatherPrimDimN 1 K 0 gs)
    (allGatherPrimDimN 1 K 0 xs) d3 ((q * (d1 * K) + (r * d1 + p)) * d2 + u) j [d2, d1 * K, d0]
    (by rw [hfullShape]; rfl) hd3 hj
    (by rw [hfullShape]; simpa [prodShape, Nat.mul_assoc] using hboundCanonical)]
  rw [bwsg_pure_row (gs.getD r (zeroTensor [d0, d1, d2, d3]))
    (xs.getD r (zeroTensor [d0, d1, d2, d3])) d3 ((q * d1 + p) * d2 + u) j [d2, d1, d0]
    (by rw [hxr]; rfl) hd3 hj
    (by rw [hxr]; simpa [prodShape, Nat.mul_assoc] using hlocal)]
  have hsum :
      (∑ z ∈ Finset.range d3,
        valAt (allGatherPrimDimN 1 K 0 xs) (((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + z) *
          valAt (allGatherPrimDimN 1 K 0 gs) (((q * (d1 * K) + (r * d1 + p)) * d2 + u) * d3 + z)) =
      ∑ z ∈ Finset.range d3,
        valAt (xs.getD r (zeroTensor [d0, d1, d2, d3])) (((q * d1 + p) * d2 + u) * d3 + z) *
          valAt (gs.getD r (zeroTensor [d0, d1, d2, d3])) (((q * d1 + p) * d2 + u) * d3 + z) := by
    apply Finset.sum_congr rfl
    intro z hz
    have hz' := Finset.mem_range.mp hz
    rw [allGatherPrimDimN_dim1_rank4_valAt xs K d0 d1 d2 d3 q r p u z
      hK hd1 hd2 hd3 hq hr hp hu hz' hhead,
      allGatherPrimDimN_dim1_rank4_valAt gs K d0 d1 d2 d3 q r p u z
      hK hd1 hd2 hd3 hq hr hp hu hz' hghead]
  rw [hsum,
    allGatherPrimDimN_dim1_rank4_valAt xs K d0 d1 d2 d3 q r p u j
      hK hd1 hd2 hd3 hq hr hp hu hj hhead,
    allGatherPrimDimN_dim1_rank4_valAt gs K d0 d1 d2 d3 q r p u j
      hK hd1 hd2 hd3 hq hr hp hu hj hghead]

private theorem bwsg_zip_softmax (gs xs : List Tensor) :
    List.zipWith softmaxBwdFromOutput gs (xs.map fw_softmax) =
      List.zipWith bw_softmax gs xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      change softmaxBwdFromOutput g (fw_softmax x) ::
          List.zipWith softmaxBwdFromOutput gs (xs.map fw_softmax) =
        bw_softmax g x :: List.zipWith bw_softmax gs xs
      rw [ih]
      rfl

/-- 任意 K 个四维分片：沿轴 1 gather 与真实输入语义的 BW_softmax 交换。 -/
theorem bw_softmax_allGatherPrimDimN_dim1_rank4
    (gs xs : List Tensor) (K b h q d : Nat)
    (hK : 0 < K) (hb : 0 < b) (hh : 0 < h) (hq : 0 < q) (hd : 0 < d)
    (hleng : gs.length = K) (hlenx : xs.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, h, q, d])
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, d]) :
    bw_softmax (allGatherPrimDimN 1 K 0 gs) (allGatherPrimDimN 1 K 0 xs) =
      allGatherPrimDimN 1 K 0 (List.zipWith bw_softmax gs xs) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlenx
    simp only [List.length_nil] at hlenx
    omega
  have hfw := fw_softmax_allGatherPrimDimN_dim1_rank4 xs b h q d hne hd hxs
  rw [hlenx] at hfw
  have hmaplen : (xs.map fw_softmax).length = K := by
    rw [List.length_map, hlenx]
  have hmapsh : ∀ y ∈ xs.map fw_softmax, y.shape = [b, h, q, d] := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    rw [fw_softmax_shape_g43, hxs x hx]
  change softmaxBwdFromOutput (allGatherPrimDimN 1 K 0 gs)
      (fw_softmax (allGatherPrimDimN 1 K 0 xs)) = _
  rw [hfw, bwsg_pure_dim1 gs (xs.map fw_softmax) K b h q d
    hK hd hleng hmaplen hgs hmapsh, bwsg_zip_softmax]

/-- 任意 K 个四维分片：沿轴 2 gather 与真实输入语义的 BW_softmax 交换。 -/
theorem bw_softmax_allGatherPrimDimN_dim2_rank4
    (gs xs : List Tensor) (K b h q d : Nat)
    (hK : 0 < K) (hb : 0 < b) (hh : 0 < h) (hq : 0 < q) (hd : 0 < d)
    (hleng : gs.length = K) (hlenx : xs.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, h, q, d])
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, d]) :
    bw_softmax (allGatherPrimDimN 2 K 0 gs) (allGatherPrimDimN 2 K 0 xs) =
      allGatherPrimDimN 2 K 0 (List.zipWith bw_softmax gs xs) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlenx
    simp only [List.length_nil] at hlenx
    omega
  have hfw := fw_softmax_allGatherPrimDimN_dim2_rank4 xs b h q d hne hd hxs
  rw [hlenx] at hfw
  have hmaplen : (xs.map fw_softmax).length = K := by
    rw [List.length_map, hlenx]
  have hmapsh : ∀ y ∈ xs.map fw_softmax, y.shape = [b, h, q, d] := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    rw [fw_softmax_shape_g43, hxs x hx]
  change softmaxBwdFromOutput (allGatherPrimDimN 2 K 0 gs)
      (fw_softmax (allGatherPrimDimN 2 K 0 xs)) = _
  rw [hfw, bwsg_pure_dim2 gs (xs.map fw_softmax) K b h q d
    hK hd hleng hmaplen hgs hmapsh, bwsg_zip_softmax]

/-- 统一 ABI：axis 仅可为 1 或 2，softmax 仍沿最后一维（轴 3）。 -/
theorem bw_softmax_allGatherPrimDimN_rank4
    (gs xs : List Tensor) (axis K b h q d : Nat)
    (haxis : axis = 1 ∨ axis = 2)
    (hK : 0 < K) (hb : 0 < b) (hh : 0 < h) (hq : 0 < q) (hd : 0 < d)
    (hleng : gs.length = K) (hlenx : xs.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, h, q, d])
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, d]) :
    bw_softmax (allGatherPrimDimN axis K 0 gs) (allGatherPrimDimN axis K 0 xs) =
      allGatherPrimDimN axis K 0 (List.zipWith bw_softmax gs xs) := by
  rcases haxis with rfl | rfl
  · exact bw_softmax_allGatherPrimDimN_dim1_rank4 gs xs K b h q d
      hK hb hh hq hd hleng hlenx hgs hxs
  · exact bw_softmax_allGatherPrimDimN_dim2_rank4 gs xs K b h q d
      hK hb hh hq hd hleng hlenx hgs hxs

end
end TrainVerify.Denote
