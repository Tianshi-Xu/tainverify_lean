import denote.KRankMatmulHeadAxis
import denote.KRankBWMatmulQuery
import denote.KRankTranspose23Extra

namespace TrainVerify.Denote

set_option maxHeartbeats 500000

/-- The last-two-axis transpose preserves ordered head-axis gathering.
The full head extent is `h * K`; the batch extent may be zero. -/
theorem transpose2d_allGather_dim1_rank4
    (K b h q n : Nat) (xs : List Tensor)
    (hK : 0 < K) (hh : 0 < h) (hq : 0 < q) (hn : 0 < n)
    (hlen : xs.length = K)
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, n]) :
    transpose2d (allGatherPrimDimN 1 K 0 xs) =
      allGatherPrimDimN 1 K 0 (xs.map transpose2d) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, h, q, n] := by
    cases xs with
    | nil => exact (hne rfl).elim
    | cons x rest => exact hxs x (List.mem_cons_self ..)
  have hgshape : (allGatherPrimDimN 1 K 0 xs).shape = [b, h * K, q, n] := by
    rw [allGatherPrimDimN_shape 1 K xs [b, h, q, n] hhead]
    simp [List.set, List.getD]
  have hmap : xs.map (transposeAxes 2 3) = xs.map transpose2d := by
    apply List.map_congr_left
    intro x hxmem
    exact (transpose2d_eq_transposeAxes23_rank4 x b h q n hh hq hn
      (hxs x hxmem)).symm
  rw [transpose2d_eq_transposeAxes23_rank4 _ b (h * K) q n
    (Nat.mul_pos hh hK) hq hn hgshape]
  have ht := transposeAxes_2_3_allGather_dim1_rank4 xs b h q n hne hxs
  rw [hlen, hmap] at ht
  exact ht

private theorem head_zipWith_bw_matmul_fst
    (gs ys : List Tensor) (x : Tensor) :
    List.zipWith fw_matmul gs (ys.map transpose2d) =
      List.zipWith (fun g y => (bw_matmul g x y).1) gs ys := by
  induction gs generalizing ys with
  | nil => cases ys <;> rfl
  | cons g rest ih =>
    cases ys with
    | nil => rfl
    | cons y tail =>
      simp only [List.map, List.zipWith, bw_matmul, batchedMatmulBwd, fw_matmul]
      exact congrArg (List.cons (batchedMatmul g (transpose2d y))) (ih tail)

private theorem head_zipWith_bw_matmul_snd
    (gs xs : List Tensor) (y : Tensor) :
    List.zipWith fw_matmul (xs.map transpose2d) gs =
      List.zipWith (fun g x => (bw_matmul g x y).2) gs xs := by
  induction xs generalizing gs with
  | nil => cases gs <;> rfl
  | cons x rest ih =>
    cases gs with
    | nil => rfl
    | cons g tail =>
      simp only [List.map, List.zipWith, bw_matmul, batchedMatmulBwd, fw_matmul]
      exact congrArg (List.cons (batchedMatmul (transpose2d x) g)) (ih tail)

/-- Head-sharded `dx = g @ yᵀ`. The unused input `x` is arbitrary and is
retained unchanged in each local call for renderer convenience. -/
theorem bw_matmul_fst_head_gather_rank4_with_unused
    (K b h q n m : Nat) (gs ys : List Tensor) (x : Tensor)
    (hK : 0 < K) (hh : 0 < h) (hq : 0 < q) (hn : 0 < n) (hm : 0 < m)
    (hgslen : gs.length = K) (hyslen : ys.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, h, q, m])
    (hys : ∀ y ∈ ys, y.shape = [b, h, n, m]) :
    (bw_matmul (allGatherPrimDimN 1 K 0 gs) x
      (allGatherPrimDimN 1 K 0 ys)).1 =
      allGatherPrimDimN 1 K 0
        (List.zipWith (fun g y => (bw_matmul g x y).1) gs ys) := by
  have htlen : (ys.map transpose2d).length = K := by
    rw [List.length_map, hyslen]
  have htshapes : ∀ t ∈ ys.map transpose2d, t.shape = [b, h, m, n] := by
    intro t ht
    obtain ⟨y, hymem, rfl⟩ := List.mem_map.mp ht
    simp only [transpose2d, hys y hymem, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Tensor.mkShape]
  have hcommute := fw_matmul_allGatherPrimDimN_dim1_aligned_K_rank4
    gs (ys.map transpose2d) K b h q m n hK hh hq hm hn
    hgslen htlen hgs htshapes
  rw [head_zipWith_bw_matmul_fst gs ys x] at hcommute
  change fw_matmul (allGatherPrimDimN 1 K 0 gs)
    (transpose2d (allGatherPrimDimN 1 K 0 ys)) = _
  rw [transpose2d_allGather_dim1_rank4 K b h n m ys hK hh hn hm hyslen hys]
  exact hcommute

/-- Head-sharded `dy = xᵀ @ g`. Unlike query sharding, head sharding
reconstructs this projection by gathering, not reduction. The unused `y`
is arbitrary and is retained unchanged in each local call. -/
theorem bw_matmul_snd_head_gather_rank4_with_unused
    (K b h q n m : Nat) (gs xs : List Tensor) (y : Tensor)
    (hK : 0 < K) (hh : 0 < h) (hq : 0 < q) (hn : 0 < n) (hm : 0 < m)
    (hgslen : gs.length = K) (hxslen : xs.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, h, q, m])
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, n]) :
    (bw_matmul (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) y).2 =
      allGatherPrimDimN 1 K 0
        (List.zipWith (fun g x => (bw_matmul g x y).2) gs xs) := by
  have htlen : (xs.map transpose2d).length = K := by
    rw [List.length_map, hxslen]
  have htshapes : ∀ t ∈ xs.map transpose2d, t.shape = [b, h, n, q] := by
    intro t ht
    obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp ht
    simp only [transpose2d, hxs x hxmem, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Tensor.mkShape]
  have hcommute := fw_matmul_allGatherPrimDimN_dim1_aligned_K_rank4
    (xs.map transpose2d) gs K b h n q m hK hh hn hq hm
    htlen hgslen htshapes hgs
  rw [head_zipWith_bw_matmul_snd gs xs y] at hcommute
  change fw_matmul (transpose2d (allGatherPrimDimN 1 K 0 xs))
    (allGatherPrimDimN 1 K 0 gs) = _
  rw [transpose2d_allGather_dim1_rank4 K b h q n xs hK hh hq hn hxslen hxs]
  exact hcommute

/-- Both input operands and the cotangent are aligned head shards, in the
same ordered rank list. The first projection ignores `xs`, so its local
unused operand is canonically `zeroTensor []`. -/
theorem bw_matmul_fst_head_gather_rank4
    (K b h q n m : Nat) (gs xs ys : List Tensor)
    (hK : 0 < K) (hh : 0 < h) (hq : 0 < q) (hn : 0 < n) (hm : 0 < m)
    (hgslen : gs.length = K) (_hxslen : xs.length = K) (hyslen : ys.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, h, q, m])
    (_hxs : ∀ x ∈ xs, x.shape = [b, h, q, n])
    (hys : ∀ y ∈ ys, y.shape = [b, h, n, m]) :
    (bw_matmul (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) (allGatherPrimDimN 1 K 0 ys)).1 =
      allGatherPrimDimN 1 K 0
        (List.zipWith (fun g y => (bw_matmul g (zeroTensor []) y).1) gs ys) := by
  exact bw_matmul_fst_head_gather_rank4_with_unused K b h q n m gs ys
    (allGatherPrimDimN 1 K 0 xs) hK hh hq hn hm hgslen hyslen hgs hys

/-- The second projection uses aligned cotangent/input pairs and ignores
`ys`, so its local unused operand is canonically `zeroTensor []`. -/
theorem bw_matmul_snd_head_gather_rank4
    (K b h q n m : Nat) (gs xs ys : List Tensor)
    (hK : 0 < K) (hh : 0 < h) (hq : 0 < q) (hn : 0 < n) (hm : 0 < m)
    (hgslen : gs.length = K) (hxslen : xs.length = K) (_hyslen : ys.length = K)
    (hgs : ∀ g ∈ gs, g.shape = [b, h, q, m])
    (hxs : ∀ x ∈ xs, x.shape = [b, h, q, n])
    (_hys : ∀ y ∈ ys, y.shape = [b, h, n, m]) :
    (bw_matmul (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) (allGatherPrimDimN 1 K 0 ys)).2 =
      allGatherPrimDimN 1 K 0
        (List.zipWith (fun g x => (bw_matmul g x (zeroTensor [])).2) gs xs) := by
  exact bw_matmul_snd_head_gather_rank4_with_unused K b h q n m gs xs
    (allGatherPrimDimN 1 K 0 ys) hK hh hq hn hm hgslen hxslen hgs hxs

end TrainVerify.Denote

#print axioms TrainVerify.Denote.transpose2d_allGather_dim1_rank4
#print axioms TrainVerify.Denote.bw_matmul_fst_head_gather_rank4_with_unused
#print axioms TrainVerify.Denote.bw_matmul_snd_head_gather_rank4_with_unused
#print axioms TrainVerify.Denote.bw_matmul_fst_head_gather_rank4
#print axioms TrainVerify.Denote.bw_matmul_snd_head_gather_rank4
