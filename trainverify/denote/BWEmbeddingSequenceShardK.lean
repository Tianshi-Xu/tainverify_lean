import denote.KRankLayernormGather

namespace TrainVerify.Denote

noncomputable section

open scoped BigOperators

namespace BWEmbeddingSequenceShardK

/-- Sequence chunking preserves the batch coordinate and offsets only the
sequence coordinate.  The rank is in range, so rank wrapping is inactive. -/
theorem chunk_ids_valAt
    (K b s : Nat) (ids : Tensor) (r q p : Nat)
    (hK : 0 < K) (hs : 0 < s)
    (hids : ids.shape = [b, s * K])
    (hr : r < K) (hq : q < b) (hp : p < s) :
    valAt (chunkPrimDimN 1 K r ids) (q * s + p) =
      valAt ids (q * (s * K) + (r * s + p)) := by
  have hdiv : s * K / K = s := by
    rw [Nat.mul_comm s K]
    exact Nat.mul_div_cancel_left s hK
  have hshape : (chunkPrimDimN 1 K r ids).shape = [b, s] := by
    rw [chunkPrimDimN_shape 1 K r ids [b, s * K] hids (Nat.ne_of_gt hK)]
    simp [List.set, List.getD, hdiv]
  have hidx : q * s + p < b * s := by
    calc
      q * s + p < (q + 1) * s := by rw [Nat.add_mul]; omega
      _ ≤ b * s := Nat.mul_le_mul_right s (Nat.succ_le_iff.mpr hq)
  have hqdiv : (q * s + p) / s = q := by
    rw [show q * s + p = p + s * q by ring,
      Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt hp, Nat.zero_add]
  have hpmod : (q * s + p) % s = p := by
    rw [show q * s + p = p + s * q by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  rw [valAt_of_lt _ _ (by rw [hshape]; simpa [prodShape] using hidx)]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hids, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, if_neg (Nat.ne_of_gt hK), hdiv,
    Nat.mul_one, if_neg (Nat.ne_of_gt hs), Nat.mod_eq_of_lt hr,
    Nat.one_ne_zero, if_false, Nat.div_one, Nat.mod_one, Nat.add_zero,
    hqdiv, hpmod]

private theorem map_range_sum (K : Nat) (f : Nat → Scalar) :
    ((List.range K).map f).sum = ∑ r ∈ Finset.range K, f r := by
  induction K with
  | zero => simp
  | succ K ih =>
      simp only [List.range_succ, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Finset.sum_range_succ, ih]

private theorem tensorSum_range_shape
    (K : Nat) (f : Nat → Tensor) (sh : Shape)
    (hK : 0 < K) (hf : ∀ r, r < K → (f r).shape = sh) :
    (tensorSum ((List.range K).map f)).shape = sh := by
  have hne : (List.range K).map f ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [List.length_map, List.length_range, List.length_nil] at hl
    omega
  obtain ⟨x, xs, he⟩ := List.exists_cons_of_ne_nil hne
  have hx : x ∈ (List.range K).map f := by rw [he]; simp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  rw [he, tensorSum_shape]
  exact hf r (List.mem_range.mp hr)

private theorem tensorSum_range_valAt
    (K : Nat) (f : Nat → Tensor) (idx : Nat)
    (hidx : idx < prodShape (tensorSum ((List.range K).map f)).shape) :
    valAt (tensorSum ((List.range K).map f)) idx =
      ∑ r ∈ Finset.range K, valAt (f r) idx := by
  have hfold : valAt (tensorSum ((List.range K).map f)) idx =
      ((List.range K).map f).foldl (fun acc t => acc + valAt t idx) 0 := by
    cases he : (List.range K).map f with
    | nil =>
        rw [valAt_of_lt _ _ hidx]
        simp only [he, tensorSum, Tensor.mkShape, List.foldl_nil]
    | cons x xs =>
        rw [valAt_of_lt _ _ hidx]
        simp only [he, tensorSum, Tensor.mkShape]
  rw [hfold, List.foldl_map, List.foldl_add_eq_sum]
  exact map_range_sum K (fun r => valAt (f r) idx)

end BWEmbeddingSequenceShardK

/-- Backward embedding over an ordered K-rank sequence gather is the sum
of the local weight gradients with correspondingly chunked IDs.

All dimensions and the rank count are arbitrary.  In particular, the batch
axis is not flattened across ranks: the proof splits the global position
sum into batch/rank/local-position sums, commutes batch and rank, and then
reassembles each rank's local batch/position sum. -/
theorem bw_embedding_seqchunk_K
    (K b s h v : Nat) (gs : List Tensor) (ids w : Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hh : 0 < h) (hv : 0 < v)
    (hlen : gs.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, s, h])
    (hids : ids.shape = [b, s * K]) (hw : w.shape = [v, h]) :
    bw_embedding (allGatherPrimDimN 1 K 0 gs) ids w =
      tensorSum ((List.range K).map (fun r =>
        bw_embedding (gs.getD r (zeroTensor [b, s, h]))
          (chunkPrimDimN 1 K r ids) w)) := by
  classical
  have hnonempty : gs ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hhead : (gs.head?.map (fun t => t.shape)).getD [] = [b, s, h] := by
    obtain ⟨g, rest, he⟩ := List.exists_cons_of_ne_nil hnonempty
    rw [he]
    simp only [List.head?, Option.map, Option.getD]
    exact hgs g (by rw [he]; simp)
  have hdiv : s * K / K = s := by
    rw [Nat.mul_comm s K]
    exact Nat.mul_div_cancel_left s hK
  have hcshape : ∀ r, (chunkPrimDimN 1 K r ids).shape = [b, s] := by
    intro r
    rw [chunkPrimDimN_shape 1 K r ids [b, s * K] hids (Nat.ne_of_gt hK)]
    simp [List.set, List.getD, hdiv]
  have hlast : lastD w.shape = h := by rw [hw]; rfl
  have hprod : prodShape ids.shape = b * (s * K) := by
    rw [hids]
    simp only [prodShape, List.foldl, Nat.one_mul]
  let localBW : Nat → Tensor := fun r =>
    bw_embedding (gs.getD r (zeroTensor [b, s, h])) (chunkPrimDimN 1 K r ids) w
  have hrshape : (tensorSum ((List.range K).map localBW)).shape = w.shape :=
    BWEmbeddingSequenceShardK.tensorSum_range_shape K localBW w.shape hK
      (fun r _ => bw_embedding_shape _ _ w)
  change bw_embedding (allGatherPrimDimN 1 K 0 gs) ids w =
    tensorSum ((List.range K).map localBW)
  apply Tensor.ext
  · rw [bw_embedding_shape, hrshape]
  · intro idx hidx
    have hidxw : idx < prodShape w.shape := by
      rwa [bw_embedding_shape] at hidx
    have hj : idx % h < h := Nat.mod_lt idx hh
    let F : Nat → Scalar := fun k =>
      if scalarToNat (valAt ids k) = idx / h then
        valAt (allGatherPrimDimN 1 K 0 gs) (k * h + idx % h) else 0
    have hfull :
        valAt (bw_embedding (allGatherPrimDimN 1 K 0 gs) ids w) idx =
          ∑ k ∈ Finset.range (b * (s * K)), F k := by
      simpa only [hlast, hprod] using
        (bw_embedding_valAt (allGatherPrimDimN 1 K 0 gs) ids w idx hidxw)
    have hlocal : ∀ r, r < K →
        valAt (localBW r) idx =
          ∑ q ∈ Finset.range b, ∑ p ∈ Finset.range s,
            F (q * (s * K) + (r * s + p)) := by
      intro r hr
      change valAt (bw_embedding _ _ w) idx = _
      rw [bw_embedding_valAt _ _ _ _ hidxw]
      have hcprod : prodShape (chunkPrimDimN 1 K r ids).shape = b * s := by
        rw [hcshape r]
        simp only [prodShape, List.foldl, Nat.one_mul]
      simp only [hlast, hcprod]
      rw [Finset.sum_range_mul_eq_sum_sum b s]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      have hq' := Finset.mem_range.mp hq
      have hp' := Finset.mem_range.mp hp
      dsimp only [F]
      rw [BWEmbeddingSequenceShardK.chunk_ids_valAt K b s ids r q p
        hK hs hids hr hq' hp']
      rw [allGatherPrimDimN_dim1_3d_valAt gs K b s h q r p (idx % h)
        hK hs hh hq' hr hp' hj hhead]
    rw [hfull, BWEmbeddingSequenceShardK.tensorSum_range_valAt K localBW idx
      (by rw [hrshape]; exact hidxw)]
    calc
      (∑ k ∈ Finset.range (b * (s * K)), F k) =
          ∑ q ∈ Finset.range b, ∑ r ∈ Finset.range K,
            ∑ p ∈ Finset.range s, F (q * (s * K) + (r * s + p)) := by
        rw [Finset.sum_range_mul_eq_sum_sum b (s * K)]
        apply Finset.sum_congr rfl
        intro q _
        have hsplit := Finset.sum_range_mul_eq_sum_sum K s
          (fun t => F (q * (s * K) + t))
        simpa only [Nat.mul_comm K s] using hsplit
      _ = ∑ r ∈ Finset.range K, ∑ q ∈ Finset.range b,
            ∑ p ∈ Finset.range s, F (q * (s * K) + (r * s + p)) :=
        Finset.sum_comm
      _ = ∑ r ∈ Finset.range K, valAt (localBW r) idx := by
        apply Finset.sum_congr rfl
        intro r hr
        exact (hlocal r (Finset.mem_range.mp hr)).symm

end

end TrainVerify.Denote
