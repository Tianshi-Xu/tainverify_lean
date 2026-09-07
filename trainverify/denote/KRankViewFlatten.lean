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
          rw [hshape x (by simp only [List.mem_cons, self_eq_true, true_or])]
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
    hshape x0 (by simp only [List.mem_cons, self_eq_true, true_or])
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

end

end TrainVerify.Denote
