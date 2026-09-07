import denote.Denote

namespace TrainVerify.Denote

noncomputable section

-- Reshaping preserves every zero-extended flat read when element counts agree.
private theorem viewFlatten_valAt_of_prod
    (target : Shape) (x : Tensor) (idx : Nat)
    (hprod : prodShape target = prodShape x.shape) :
    valAt (fw_view target x) idx = valAt x idx := by
  unfold fw_view valAt
  simp only [Tensor.mkShape]
  split <;> split <;> simp_all

-- Include out-of-range ranks: both gather defaults have zero flat values.
private theorem viewFlatten_map_getD_valAt
    (b s n d : Nat) (xs : List Tensor) (r idx : Nat) :
    (∀ x ∈ xs, x.shape = [b, s, n, d]) →
    valAt ((xs.map (fun x => fw_view [b, s, n * d] x)).getD r
        (zeroTensor [b, s, n * d])) idx =
      valAt (xs.getD r (zeroTensor [b, s, n, d])) idx := by
  induction xs generalizing r with
  | nil =>
      intro _
      simp [List.getD, valAt, zeroTensor, Tensor.mkShape]
  | cons x rest ih =>
      intro hshape
      cases r with
      | zero =>
          simp only [List.map, List.getD, List.getElem?_cons_zero, Option.getD_some]
          apply viewFlatten_valAt_of_prod
          rw [hshape x (List.mem_cons_self ..)]
          simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
      | succ r =>
          have hrest : ∀ y ∈ rest, y.shape = [b, s, n, d] := by
            intro y hy
            exact hshape y (List.mem_cons_of_mem x hy)
          simpa only [List.map, List.getD, List.getElem?_cons_succ] using ih r hrest

/-- Flattening the last two axes of rank-four shards commutes with a
sequence-axis gather. This is the `fw_view` denotation used by `BW_view`:
`[b,s,n,d]` becomes `[b,s,n*d]`, while dimension 1 is gathered over `K` ranks.
The proof compares actual flat values, not an assumed value relation. -/
theorem fw_view_allGatherPrimDimN_dim1_rank4_to_rank3
    (K b s n d : Nat) (xs : List Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hn : 0 < n) (hd : 0 < d)
    (hlen : xs.length = K)
    (hshape : ∀ x ∈ xs, x.shape = [b, s, n, d]) :
    fw_view [b, s * K, n * d] (allGatherPrimDimN 1 K 0 xs) =
      allGatherPrimDimN 1 K 0 (xs.map (fun x => fw_view [b, s, n * d] x)) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  obtain ⟨x0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hx0 : x0.shape = [b, s, n, d] :=
    hshape x0 (List.mem_cons_self ..)
  have hhead : ((x0 :: rest).head?.map (fun t => t.shape)).getD [] =
      [b, s, n, d] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hx0
  have hmapHead :
      ((((x0 :: rest).map (fun x => fw_view [b, s, n * d] x)).head?.map
        (fun t => t.shape)).getD []) = [b, s, n * d] := by
    rfl
  have hfullShape : (allGatherPrimDimN 1 K 0 (x0 :: rest)).shape =
      [b, s * K, n, d] := by
    rw [allGatherPrimDimN_shape 1 K _ [b, s, n, d] hhead]
    rfl
  have hrhsShape :
      (allGatherPrimDimN 1 K 0
        ((x0 :: rest).map (fun x => fw_view [b, s, n * d] x))).shape =
      [b, s * K, n * d] := by
    rw [allGatherPrimDimN_shape 1 K _ [b, s, n * d] hmapHead]
    rfl
  have hprod : prodShape [b, s * K, n * d] =
      prodShape (allGatherPrimDimN 1 K 0 (x0 :: rest)).shape := by
    rw [hfullShape]
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
  apply Tensor.ext
  · change [b, s * K, n * d] = _
    exact hrhsShape.symm
  · intro idx hidx
    change idx < prodShape [b, s * K, n * d] at hidx
    rw [viewFlatten_valAt_of_prod _ _ idx hprod]
    have hleft : idx < prodShape (allGatherPrimDimN 1 K 0 (x0 :: rest)).shape := by
      rw [← hprod]
      exact hidx
    have hright : idx < prodShape (allGatherPrimDimN 1 K 0
        ((x0 :: rest).map (fun x => fw_view [b, s, n * d] x))).shape := by
      rw [hrhsShape]
      exact hidx
    rw [valAt_of_lt _ idx hleft, valAt_of_lt _ idx hright]
    unfold allGatherPrimDimN
    simp only [hhead, hmapHead, List.drop, List.foldl, Tensor.mkShape,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Nat.one_mul]
    -- Both kernels now use postStride = n*d and hence identical rank and
    -- local flat-index expressions. Only the selected shard is reshaped.
    exact (viewFlatten_map_getD_valAt b s n d (x0 :: rest) _ _ hshape).symm

/-- Flattening the last two axes commutes with gathering the head axis.
The dimension-2 gather concatenates `[b,s,n,d]` head shards before viewing
as `[b,s,(n*K)*d]`, or equivalently concatenates their `[b,s,n*d]` views.
Both the selected rank and its local flat value are proved equal. -/
theorem fw_view_allGatherPrimDimN_dim2_rank4_to_rank3
    (K b s n d : Nat) (xs : List Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hn : 0 < n) (hd : 0 < d)
    (hlen : xs.length = K)
    (hshape : ∀ x ∈ xs, x.shape = [b, s, n, d]) :
    fw_view [b, s, (n * K) * d] (allGatherPrimDimN 2 K 0 xs) =
      allGatherPrimDimN 2 K 0 (xs.map (fun x => fw_view [b, s, n * d] x)) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  obtain ⟨x0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hx0 : x0.shape = [b, s, n, d] :=
    hshape x0 (List.mem_cons_self ..)
  have hhead : ((x0 :: rest).head?.map (fun t => t.shape)).getD [] =
      [b, s, n, d] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hx0
  have hmapHead :
      ((((x0 :: rest).map (fun x => fw_view [b, s, n * d] x)).head?.map
        (fun t => t.shape)).getD []) = [b, s, n * d] := by
    rfl
  have hstride : (n * K) * d = (n * d) * K := by ac_rfl
  have hfullShape : (allGatherPrimDimN 2 K 0 (x0 :: rest)).shape =
      [b, s, n * K, d] := by
    rw [allGatherPrimDimN_shape 2 K _ [b, s, n, d] hhead]
    rfl
  have hrhsShape :
      (allGatherPrimDimN 2 K 0
        ((x0 :: rest).map (fun x => fw_view [b, s, n * d] x))).shape =
      [b, s, (n * K) * d] := by
    rw [allGatherPrimDimN_shape 2 K _ [b, s, n * d] hmapHead]
    change [b, s, (n * d) * K] = [b, s, (n * K) * d]
    rw [hstride]
  have hprod : prodShape [b, s, (n * K) * d] =
      prodShape (allGatherPrimDimN 2 K 0 (x0 :: rest)).shape := by
    rw [hfullShape]
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  have hnd0 : n * d ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hn hd)
  have hfull0 : (n * K) * d ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos hn hK) hd)
  apply Tensor.ext
  · change [b, s, (n * K) * d] = _
    exact hrhsShape.symm
  · intro idx hidx
    change idx < prodShape [b, s, (n * K) * d] at hidx
    rw [viewFlatten_valAt_of_prod _ _ idx hprod]
    have hleft : idx < prodShape (allGatherPrimDimN 2 K 0 (x0 :: rest)).shape := by
      rw [← hprod]
      exact hidx
    have hright : idx < prodShape (allGatherPrimDimN 2 K 0
        ((x0 :: rest).map (fun x => fw_view [b, s, n * d] x))).shape := by
      rw [hrhsShape]
      exact hidx
    rw [valAt_of_lt _ idx hleft, valAt_of_lt _ idx hright]
    unfold allGatherPrimDimN
    simp only [hhead, hmapHead, List.drop, List.foldl, Tensor.mkShape,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Nat.one_mul, Nat.mul_one, ← hstride,
      if_neg hn0, if_neg hd0, if_neg hnd0, if_neg hfull0,
      Nat.one_ne_zero, if_false, Nat.div_one, Nat.mod_one, Nat.add_zero]
    let remainder := idx % ((n * K) * d)
    let pre := idx / ((n * K) * d)
    change valAt ((x0 :: rest).getD (remainder / d / n)
        (zeroTensor [b, s, n, d]))
        (pre * (n * d) + (remainder / d % n) * d + remainder % d) =
      valAt (((x0 :: rest).map (fun x => fw_view [b, s, n * d] x)).getD
        (remainder / (n * d)) (zeroTensor [b, s, n * d]))
        (pre * (n * d) + remainder % (n * d))
    have hrank : remainder / d / n = remainder / (n * d) := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm d n]
    have hrem : (remainder / d % n) * d + remainder % d =
        remainder % (n * d) := by
      rw [Nat.mul_comm n d, Nat.mod_mul]
      ring
    rw [hrank, Nat.add_assoc, hrem]
    exact (viewFlatten_map_getD_valAt b s n d (x0 :: rest) _ _ hshape).symm

end

end TrainVerify.Denote
