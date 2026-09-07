import denote.KRankMatmulContractionReduction
import denote.KRankTranspose

namespace TrainVerify.Denote

set_option maxHeartbeats 500000

/-- On rank four, the backward-matmul transpose is the last-two-axis swap. -/
theorem transpose2d_eq_transposeAxes23_rank4
    (x : Tensor) (b h q n : Nat)
    (hh : 0 < h) (hq : 0 < q) (hn : 0 < n)
    (hx : x.shape = [b, h, q, n]) :
    transpose2d x = transposeAxes 2 3 x := by
  have htshape : (transpose2d x).shape = [b, h, n, q] := by
    simp only [transpose2d, hx, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Tensor.mkShape]
  have hashape : (transposeAxes 2 3 x).shape = [b, h, n, q] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  apply Tensor.ext (by rw [htshape, hashape])
  intro idx hidx
  have hbound : idx < b * h * n * q := by
    rw [htshape] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  rw [transposeAxes_2_3_valAt_gen x b h q n idx hx
    (Nat.ne_of_gt hh) (Nat.ne_of_gt hq) (Nat.ne_of_gt hn) hbound]
  have htbound : idx < prodShape (transpose2d x).shape := by
    rw [htshape]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hbound
  rw [valAt_of_lt _ _ htbound]
  simp only [transpose2d, hx, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, Tensor.mkShape,
    if_neg (Nat.ne_of_gt (Nat.mul_pos hq hn)), if_neg (Nat.ne_of_gt hq)]
  rw [Nat.mul_comm q n]
  have hmod : idx % (h * n * q) % (n * q) = idx % (n * q) := by
    apply Nat.mod_mod_of_dvd
    exact ⟨h, by ring⟩
  rw [hmod]
  have hbig : idx / (h * n * q) * (h * n * q) + idx % (h * n * q) = idx := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod idx (h * n * q)
  have hsmall : idx % (h * n * q) / (n * q) * (n * q) + idx % (n * q) =
      idx % (h * n * q) := by
    have he := Nat.div_add_mod (idx % (h * n * q)) (n * q)
    rw [hmod] at he
    simpa only [Nat.mul_comm] using he
  have hfull : idx / (n * q) * (n * q) + idx % (n * q) = idx := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod idx (n * q)
  congr 1
  nlinarith only [hbig, hsmall, hfull]

/-- Query-axis gathering becomes contraction-axis gathering after the transpose
used by `BW_matmul`. The rank order is unchanged. -/
theorem transpose2d_allGather_dim2_to_dim3_rank4
    (K b h q n : Nat) (xs : List Tensor)
    (hK : 0 < K) (hh : 0 < h) (hq : 0 < q) (hn : 0 < n)
    (hlen : xs.length = K)
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, n]) :
    transpose2d (allGatherPrimDimN 2 K 0 xs) =
      allGatherPrimDimN 3 K 0 (xs.map transpose2d) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, h, q, n] := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons x rest => exact hxs x (List.mem_cons_self ..)
  have hgshape : (allGatherPrimDimN 2 K 0 xs).shape = [b, h, q * K, n] := by
    rw [allGatherPrimDimN_shape 2 K xs [b, h, q, n] hhead]
    simp [List.set, List.getD]
  have hmap : xs.map (transposeAxes 2 3) = xs.map transpose2d := by
    apply List.map_congr_left
    intro x hxmem
    exact (transpose2d_eq_transposeAxes23_rank4 x b h q n hh hq hn
      (hxs x hxmem)).symm
  rw [transpose2d_eq_transposeAxes23_rank4 _ b h (q * K) n hh
    (Nat.mul_pos hq hK) hn hgshape]
  have ht := transposeAxes_2_3_allGather_dim2_to_dim3_rank4 xs b h q n hne hxs
  rw [hlen, hmap] at ht
  exact ht

/-- The shared-right-operand gradient reduces over query shards. No property of
`y` is needed: the second component of `bw_matmul g x y` is `xᵀ @ g`.
The batch size `b` may be zero; the remaining dimensions and rank count are positive. -/
theorem bw_matmul_snd_query_reduction_rank4
    (K b h q n m : Nat) (gs xs : List Tensor) (y : Tensor)
    (hK : 0 < K) (hh : 0 < h) (hq : 0 < q) (hn : 0 < n) (hm : 0 < m)
    (hgslen : gs.length = K) (hxslen : xs.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, h, q, m])
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, n]) :
    (bw_matmul (allGatherPrimDimN 2 K 0 gs)
      (allGatherPrimDimN 2 K 0 xs) y).2 =
      tensorSum (List.zipWith (fun g x => (bw_matmul g x y).2) gs xs) := by
  have htlen : (xs.map transpose2d).length = K := by
    rw [List.length_map, hxslen]
  have htshapes : ∀ t ∈ xs.map transpose2d, t.shape = [b, h, n, q] := by
    intro t ht
    obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp ht
    simp only [transpose2d, hxs x hxmem, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Tensor.mkShape]
  have hreduce := fw_matmul_allGather_contraction_eq_allReduce_zipWith_rank4
    (xs.map transpose2d) gs K b h n q m hK hn hq hm
    htlen hgslen htshapes hgs
  have hzip : List.zipWith fw_matmul (xs.map transpose2d) gs =
      List.zipWith (fun g x => (bw_matmul g x y).2) gs xs := by
    clear hreduce htshapes htlen hgs hxs hgslen hxslen
    induction xs generalizing gs with
    | nil => cases gs <;> rfl
    | cons x rest ih =>
      cases gs with
      | nil => rfl
      | cons g tail =>
        simp only [List.map, List.zipWith, bw_matmul, batchedMatmulBwd, fw_matmul]
        exact congrArg (List.cons (batchedMatmul (transpose2d x) g)) (ih tail)
  rw [hzip] at hreduce
  have hsum : allReducePrim K 0
      (List.zipWith (fun g x => (bw_matmul g x y).2) gs xs) =
      tensorSum (List.zipWith (fun g x => (bw_matmul g x y).2) gs xs) := by
    cases List.zipWith (fun g x => (bw_matmul g x y).2) gs xs <;> rfl
  rw [hsum] at hreduce
  change fw_matmul (transpose2d (allGatherPrimDimN 2 K 0 xs))
    (allGatherPrimDimN 2 K 0 gs) = _
  rw [transpose2d_allGather_dim2_to_dim3_rank4 K b h q n xs
    hK hh hq hn hxslen hxs]
  exact hreduce

end TrainVerify.Denote

#print axioms TrainVerify.Denote.bw_matmul_snd_query_reduction_rank4
