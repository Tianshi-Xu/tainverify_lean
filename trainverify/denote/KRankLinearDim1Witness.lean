import denote.Denote

namespace TrainVerify.Denote

/-- Generic pointwise semantics of a dimension-1 all-gather on 3D shards. -/
theorem allGatherPrimDimN1_3d_valAt
    (K b s i : Nat) (xs : List Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hi : 0 < i)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, i])
    (batch : Nat) (hbatch : batch < b)
    (r : Nat) (hr : r < K) (p : Nat) (hp : p < s)
    (j : Nat) (hj : j < i) :
    valAt (allGatherPrimDimN 1 K 0 xs)
      ((batch * (s * K) + (r * s + p)) * i + j) =
    valAt (xs.getD r (zeroTensor [b, s, i]))
      ((batch * s + p) * i + j) := by
  have hsK : 0 < s * K := Nat.mul_pos hs hK
  have hsKi : 0 < s * K * i := Nat.mul_pos hsK hi
  have hsi : 0 < s * i := Nat.mul_pos hs hi
  have hrp : r * s + p < s * K := by
    have hlt : r * s + p < (r + 1) * s := by
      calc
        r * s + p < r * s + s := Nat.add_lt_add_left hp _
        _ = (r + 1) * s := by ring
    have hle : (r + 1) * s ≤ K * s := Nat.mul_le_mul_right s hr
    calc
      r * s + p < (r + 1) * s := hlt
      _ ≤ K * s := hle
      _ = s * K := by ring
  have hlow : (r * s + p) * i + j < s * K * i := by
    calc
      (r * s + p) * i + j < (r * s + p) * i + i := Nat.add_lt_add_left hj _
      _ = (r * s + p + 1) * i := by ring
      _ ≤ (s * K) * i := Nat.mul_le_mul_right i hrp
  have hidx_eq : (batch * (s * K) + (r * s + p)) * i + j =
      ((r * s + p) * i + j) + (s * K * i) * batch := by ring
  have hidx : (batch * (s * K) + (r * s + p)) * i + j < b * (s * K) * i := by
    rw [hidx_eq]
    calc
      ((r * s + p) * i + j) + (s * K * i) * batch
          < (s * K * i) + (s * K * i) * batch := Nat.add_lt_add_right hlow _
      _ = (batch + 1) * (s * K * i) := by ring
      _ ≤ b * (s * K * i) := Nat.mul_le_mul_right (s * K * i) hbatch
      _ = b * (s * K) * i := by ring
  have hgather_shape : (allGatherPrimDimN 1 K 0 xs).shape = [b, s * K, i] := by
    rw [allGatherPrimDimN_shape 1 K xs [b, s, i] hhead]
    simp [List.set, List.getD]
  have hprod : (batch * (s * K) + (r * s + p)) * i + j <
      prodShape (allGatherPrimDimN 1 K 0 xs).shape := by
    rw [hgather_shape]
    simpa [prodShape] using hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN
  simp only [hhead, Tensor.mkShape, List.getD_cons_succ, List.getD_cons_zero,
    List.drop, List.foldl, Nat.one_mul,
    show i ≠ 0 from Nat.ne_of_gt hi,
    show s ≠ 0 from Nat.ne_of_gt hs,
    show s * K ≠ 0 from Nat.ne_of_gt hsK,
    show s * K * i ≠ 0 from Nat.ne_of_gt hsKi,
    show s * i ≠ 0 from Nat.ne_of_gt hsi,
    ite_false]
  have hdivFull : ((batch * (s * K) + (r * s + p)) * i + j) /
      (s * K * i) = batch := by
    rw [hidx_eq,
      Nat.add_mul_div_left _ _ hsKi, Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hmodFull : ((batch * (s * K) + (r * s + p)) * i + j) %
      (s * K * i) = (r * s + p) * i + j := by
    rw [hidx_eq,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hdivI : ((r * s + p) * i + j) / i = r * s + p := by
    rw [show (r * s + p) * i + j = j + i * (r * s + p) by ring,
      Nat.add_mul_div_left _ _ hi, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmodI : ((r * s + p) * i + j) % i = j := by
    rw [show (r * s + p) * i + j = j + i * (r * s + p) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hdivS : (r * s + p) / s = r := by
    rw [show r * s + p = p + s * r by ring,
      Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt hp, Nat.zero_add]
  have hmodS : (r * s + p) % s = p := by
    rw [show r * s + p = p + s * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  rw [hdivFull, hmodFull, hdivI, hmodI, hdivS, hmodS]
  congr 1
  ring

/-- A genuinely rank-parameterized 3D linear/all-gather commutation theorem on dim 1. -/
theorem fw_linear_3d_allGatherPrimDimN_dim1_comm
    (K b s i o : Nat) (xs : List Tensor) (w : Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hi : 0 < i) (ho : 0 < o)
    (hlen : xs.length = K)
    (hshape : ∀ x ∈ xs, x.shape = [b, s, i])
    (hw : w.shape = [o, i]) :
    fw_linear (allGatherPrimDimN 1 K 0 xs) w =
      allGatherPrimDimN 1 K 0 (xs.map (fun x => fw_linear x w)) := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, i] := by
    cases hxs : xs with
    | nil => simp [hxs] at hlen; omega
    | cons x0 rest =>
      simp only [hxs, List.head?, Option.map, Option.getD]
      exact hshape x0 (hxs ▸ List.mem_cons_self ..)
  have hgather_shape : (allGatherPrimDimN 1 K 0 xs).shape = [b, s * K, i] := by
    rw [allGatherPrimDimN_shape 1 K xs [b, s, i] hhead]
    simp [List.set, List.getD]
  have hmap_head : ((xs.map (fun x => fw_linear x w)).head?.map (fun t => t.shape)).getD [] =
      [b, s, o] := by
    cases hxs : xs with
    | nil => simp [hxs] at hlen; omega
    | cons x0 rest =>
      simp only [hxs, List.map, List.head?, Option.map, Option.getD]
      exact fw_linear_3d_shape b s i o x0 w (hshape x0 (hxs ▸ List.mem_cons_self ..)) hw
  have hLHS_shape : (fw_linear (allGatherPrimDimN 1 K 0 xs) w).shape = [b, s * K, o] :=
    fw_linear_3d_shape b (s * K) i o _ w hgather_shape hw
  have hRHS_shape : (allGatherPrimDimN 1 K 0 (xs.map (fun x => fw_linear x w))).shape =
      [b, s * K, o] := by
    rw [allGatherPrimDimN_shape 1 K _ [b, s, o] hmap_head]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  simp only [prodShape, List.foldl, Nat.one_mul] at hidx
  have hsK : 0 < s * K := Nat.mul_pos hs hK
  have hsKo : 0 < s * K * o := Nat.mul_pos hsK ho
  set batch := idx / (s * K * o)
  set rem := idx % (s * K * o)
  set seq := rem / o
  set col := rem % o
  set r := seq / s
  set p := seq % s
  have hbatch : batch < b := by
    change idx / (s * K * o) < b
    apply Nat.div_lt_of_lt_mul
    calc idx < b * (s * K) * o := hidx
      _ = (s * K * o) * b := by ring
  have hrem : rem < s * K * o := Nat.mod_lt _ hsKo
  have hseq : seq < s * K := by
    change idx % (s * K * o) / o < s * K
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm o (s * K)]
    exact hrem
  have hcol : col < o := Nat.mod_lt _ ho
  have hr : r < K := by
    change idx % (s * K * o) / o / s < K
    apply Nat.div_lt_of_lt_mul
    exact hseq
  have hp : p < s := Nat.mod_lt _ hs
  have htop : batch * (s * K * o) + rem = idx := by
    simpa [batch, rem, Nat.mul_comm] using Nat.div_add_mod idx (s * K * o)
  have hmid : seq * o + col = rem := by
    simpa [seq, col, Nat.mul_comm] using Nat.div_add_mod rem o
  have hseqdm : r * s + p = seq := by
    simpa [r, p, Nat.mul_comm] using Nat.div_add_mod seq s
  have hrp_main : r * s + p < s * K := by rw [hseqdm]; exact hseq
  have hidx_decomp : idx = (batch * (s * K) + (r * s + p)) * o + col := by
    calc
      idx = batch * (s * K * o) + rem := htop.symm
      _ = batch * (s * K * o) + (seq * o + col) := by rw [hmid]
      _ = batch * (s * K * o) + ((r * s + p) * o + col) := by rw [hseqdm]
      _ = (batch * (s * K) + (r * s + p)) * o + col := by ring
  have hr_len : r < xs.length := by omega
  have hxr_shape : (xs[r]).shape = [b, s, i] := hshape _ (List.getElem_mem hr_len)
  have hmap_getD : (xs.map (fun x => fw_linear x w)).getD r (zeroTensor [b, s, o]) =
      fw_linear xs[r] w := by
    simp [List.getD, List.getElem?_eq_getElem (by simpa [List.length_map] using hr_len),
      List.getElem_map]
  rw [hidx_decomp]
  have hLHS_val : valAt (fw_linear (allGatherPrimDimN 1 K 0 xs) w)
      ((batch * (s * K) + (r * s + p)) * o + col) =
      ∑ j ∈ Finset.range i,
        valAt (allGatherPrimDimN 1 K 0 xs)
          ((batch * (s * K) + (r * s + p)) * i + j) *
        valAt w (col * i + j) := by
    have hprod : (batch * (s * K) + (r * s + p)) * o + col <
        prodShape [b, s * K, o] := by
      rw [← hidx_decomp]
      simpa [prodShape] using hidx
    conv_lhs => simp only [fw_linear, hgather_shape, hw]
    rw [valAt_of_lt _ _ hprod]
    simp only [Tensor.mkShape, show s * K * o ≠ 0 from Nat.ne_of_gt hsKo,
      show o ≠ 0 from Nat.ne_of_gt ho, ite_false]
    have hlowO : (r * s + p) * o + col < s * K * o := by
      calc
        (r * s + p) * o + col < (r * s + p) * o + o := Nat.add_lt_add_left hcol _
        _ = (r * s + p + 1) * o := by ring
        _ ≤ (s * K) * o := Nat.mul_le_mul_right o hrp_main
    have hdiv : ((batch * (s * K) + (r * s + p)) * o + col) / (s * K * o) = batch := by
      rw [show (batch * (s * K) + (r * s + p)) * o + col =
          ((r * s + p) * o + col) + (s * K * o) * batch by ring,
        Nat.add_mul_div_left _ _ hsKo, Nat.div_eq_of_lt hlowO, Nat.zero_add]
    have hmod : ((batch * (s * K) + (r * s + p)) * o + col) % (s * K * o) =
        (r * s + p) * o + col := by
      rw [show (batch * (s * K) + (r * s + p)) * o + col =
          ((r * s + p) * o + col) + (s * K * o) * batch by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlowO]
    have hdivO : ((r * s + p) * o + col) / o = r * s + p := by
      rw [show (r * s + p) * o + col = col + o * (r * s + p) by ring,
        Nat.add_mul_div_left _ _ ho, Nat.div_eq_of_lt hcol, Nat.zero_add]
    have hmodO : ((r * s + p) * o + col) % o = col := by
      rw [show (r * s + p) * o + col = col + o * (r * s + p) by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
    rw [hdiv, hmod, hdivO, hmodO]
  have hRHS_val : valAt (allGatherPrimDimN 1 K 0 (xs.map (fun x => fw_linear x w)))
      ((batch * (s * K) + (r * s + p)) * o + col) =
      ∑ j ∈ Finset.range i,
        valAt xs[r] ((batch * s + p) * i + j) * valAt w (col * i + j) := by
    rw [allGatherPrimDimN1_3d_valAt K b s o _ hK hb hs ho hmap_head batch hbatch r hr p hp col hcol]
    rw [hmap_getD]
    have hlocal_low : p * o + col < s * o := by
      calc
        p * o + col < p * o + o := Nat.add_lt_add_left hcol _
        _ = (p + 1) * o := by ring
        _ ≤ s * o := Nat.mul_le_mul_right o hp
    have hlocal_bound : (batch * s + p) * o + col < b * s * o := by
      rw [show (batch * s + p) * o + col = (p * o + col) + (s * o) * batch by ring]
      calc
        (p * o + col) + (s * o) * batch < (s * o) + (s * o) * batch :=
          Nat.add_lt_add_right hlocal_low _
        _ = (batch + 1) * (s * o) := by ring
        _ ≤ b * (s * o) := Nat.mul_le_mul_right (s * o) hbatch
        _ = b * s * o := by ring
    have hlocal_prod : (batch * s + p) * o + col < prodShape [b, s, o] := by
      simpa [prodShape] using hlocal_bound
    conv_lhs => simp only [fw_linear, hxr_shape, hw]
    rw [valAt_of_lt _ _ hlocal_prod]
    simp only [Tensor.mkShape, show s * o ≠ 0 from Nat.ne_of_gt (Nat.mul_pos hs ho),
      show o ≠ 0 from Nat.ne_of_gt ho, ite_false]
    have hdivSO : ((batch * s + p) * o + col) / (s * o) = batch := by
      rw [show (batch * s + p) * o + col = (p * o + col) + (s * o) * batch by ring,
        Nat.add_mul_div_left _ _ (Nat.mul_pos hs ho), Nat.div_eq_of_lt hlocal_low, Nat.zero_add]
    have hmodSO : ((batch * s + p) * o + col) % (s * o) = p * o + col := by
      rw [show (batch * s + p) * o + col = (p * o + col) + (s * o) * batch by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlocal_low]
    have hdivO : (p * o + col) / o = p := by
      rw [show p * o + col = col + o * p by ring,
        Nat.add_mul_div_left _ _ ho, Nat.div_eq_of_lt hcol, Nat.zero_add]
    have hmodO : (p * o + col) % o = col := by
      rw [show p * o + col = col + o * p by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
    rw [hdivSO, hmodSO, hdivO, hmodO]
  rw [hLHS_val, hRHS_val]
  apply Finset.sum_congr rfl
  intro j hjmem
  congr 1
  have hag := allGatherPrimDimN1_3d_valAt K b s i xs hK hb hs hi hhead batch hbatch r hr p hp j
    (Finset.mem_range.mp hjmem)
  rw [show xs.getD r (zeroTensor [b, s, i]) = xs[r] by
    simp [List.getD, List.getElem?_eq_getElem hr_len]] at hag
  exact hag

#check fw_linear_3d_allGatherPrimDimN_dim1_comm
#print axioms fw_linear_3d_allGatherPrimDimN_dim1_comm

end TrainVerify.Denote
