import denote.KRankMatmulHeadAxis

/-!
# Rank-4 matmul within one DP unit

Contiguous batch chunks preserve each complete matrix product. Aligned,
ordered head shards then reconstruct via the existing TP matmul theorem.
`Q`, `K`, and `M` are independent dimensions throughout. Only predecessor
reconstruction and actual producer equations are premises; output shapes
and output reconstruction are conclusions. This is library algebra, not
an authentication of source-graph DP ownership.
-/

namespace TrainVerify.Denote

open scoped BigOperators

set_option maxHeartbeats 500000

private theorem source_matmul_pair_bound (a b n m : Nat)
    (ha : a < n) (hb : b < m) : a * m + b < n * m := by
  calc
    a * m + b < a * m + m := Nat.add_lt_add_left hb _
    _ = (a + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right m ha

private theorem source_matmul_chunk_shape
    (D u B H Q K : Nat) (x : Tensor)
    (hD : 0 < D) (hx : x.shape = [B * D, H, Q, K]) :
    (chunkPrimDimN 0 D u x).shape = [B, H, Q, K] := by
  rw [chunkPrimDimN_shape 0 D u x _ hx hD.ne']
  simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]

private theorem source_matmul_chunk0_flat
    (D u B H Q K : Nat) (x : Tensor)
    (hx : x.shape = [B * D, H, Q, K])
    (hD : 0 < D) (hu : u < D)
    (hH : 0 < H) (hQ : 0 < Q) (hK : 0 < K)
    (idx : Nat) (hi : idx < B * H * Q * K) :
    valAt (chunkPrimDimN 0 D u x) idx =
      valAt x (u * (B * H * Q * K) + idx) := by
  have hdiv : B * D / D = B := Nat.mul_div_cancel B hD
  have hshape := source_matmul_chunk_shape D u B H Q K x hD hx
  have hbound : idx < prodShape (chunkPrimDimN 0 D u x).shape := by
    rw [hshape]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  have hstride : H * Q * K ≠ 0 := (Nat.mul_pos (Nat.mul_pos hH hQ) hK).ne'
  have hlocal : idx < B * (H * Q * K) := by
    simpa only [Nat.mul_assoc] using hi
  have hnonzero : B * (H * Q * K) ≠ 0 := by omega
  rw [valAt_of_lt _ _ hbound]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hx, List.getD_cons_zero, List.drop, List.foldl,
    Nat.one_mul, hD.ne', ite_false, hdiv, Nat.mod_eq_of_lt hu,
    hstride, hnonzero]
  rw [Nat.div_eq_of_lt hlocal, Nat.mod_eq_of_lt hlocal,
    Nat.zero_mul, Nat.zero_add]
  congr 1
  calc
    (u * B + idx / (H * Q * K)) * (H * Q * K) + idx % (H * Q * K) =
        u * (B * H * Q * K) +
          ((H * Q * K) * (idx / (H * Q * K)) + idx % (H * Q * K)) := by ring
    _ = u * (B * H * Q * K) + idx := by rw [Nat.div_add_mod]

private theorem source_matmul_chunk0_valAt
    (D u B H Q K : Nat) (x : Tensor)
    (hx : x.shape = [B * D, H, Q, K])
    (hD : 0 < D) (hu : u < D)
    (hH : 0 < H) (hQ : 0 < Q) (hK : 0 < K)
    (outer i j : Nat) (ho : outer < B * H) (hi : i < Q) (hj : j < K) :
    valAt (chunkPrimDimN 0 D u x) ((outer * Q + i) * K + j) =
      valAt x (((u * (B * H) + outer) * Q + i) * K + j) := by
  have hrow := source_matmul_pair_bound outer i (B * H) Q ho hi
  have hidx := source_matmul_pair_bound (outer * Q + i) j (B * H * Q) K hrow hj
  rw [source_matmul_chunk0_flat D u B H Q K x hx hD hu hH hQ hK _ hidx]
  congr 1
  ring

/-- Matmul commutes with a legal contiguous batch chunk. `H` is the full
head count here; the unit adapter instantiates it with `H * T`. -/
theorem fw_matmul_batch_chunk_dim0_rank4
    (D u B H Q K M : Nat) (x y : Tensor)
    (hD : 0 < D) (_hB : 0 < B) (hH : 0 < H)
    (hQ : 0 < Q) (hK : 0 < K) (hM : 0 < M) (hu : u < D)
    (hx : x.shape = [B * D, H, Q, K])
    (hy : y.shape = [B * D, H, K, M]) :
    chunkPrimDimN 0 D u (fw_matmul x y) =
      fw_matmul (chunkPrimDimN 0 D u x) (chunkPrimDimN 0 D u y) := by
  have hcx := source_matmul_chunk_shape D u B H Q K x hD hx
  have hcy := source_matmul_chunk_shape D u B H K M y hD hy
  have hglobal := fw_matmul_rank4_shape x y (B * D) H Q K M hx hy
  have hleft := source_matmul_chunk_shape D u B H Q M (fw_matmul x y) hD hglobal
  have hright := fw_matmul_rank4_shape
    (chunkPrimDimN 0 D u x) (chunkPrimDimN 0 D u y) B H Q K M hcx hcy
  apply Tensor.ext (by rw [hleft, hright])
  intro idx hidx
  have hbound : idx < B * H * Q * M := by
    rw [hleft] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  let row := idx / M
  let outer := row / Q
  let i := row % Q
  let j := idx % M
  have hj : j < M := Nat.mod_lt _ hM
  have hi : i < Q := Nat.mod_lt _ hQ
  have hrow : row < B * H * Q := by
    dsimp only [row]
    rw [Nat.div_lt_iff_lt_mul hM]
    exact hbound
  have houter : outer < B * H := by
    dsimp only [outer]
    rw [Nat.div_lt_iff_lt_mul hQ]
    exact hrow
  have hrowEq : outer * Q + i = row := by
    dsimp only [outer, i]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod row Q
  have hidxEq : idx = (outer * Q + i) * M + j := by
    rw [hrowEq]
    dsimp only [row, j]
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod idx M).symm
  have hfullOuter : u * (B * H) + outer < (B * D) * H := by
    have h := source_matmul_pair_bound u outer D (B * H) hu houter
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  rw [hidxEq]
  rw [source_matmul_chunk0_valAt D u B H Q M (fw_matmul x y)
    hglobal hD hu hH hQ hM outer i j houter hi hj]
  rw [fw_matmul_rank4_valAt x y (B * D) H Q K M
    (u * (B * H) + outer) i j hM hfullOuter hi hj hx hy]
  rw [fw_matmul_rank4_valAt (chunkPrimDimN 0 D u x)
    (chunkPrimDimN 0 D u y) B H Q K M outer i j hM houter hi hj hcx hcy]
  apply Finset.sum_congr rfl
  intro l hl
  have hlK : l < K := Finset.mem_range.mp hl
  rw [source_matmul_chunk0_valAt D u B H Q K x hx hD hu hH hQ hK
    outer i l houter hi hlK]
  rw [source_matmul_chunk0_valAt D u B H K M y hy hD hu hH hK hM
    outer l j houter hlK hj]

/-- Actual global and ordered local matmul executions inherit their shapes
and reconstruct within the selected DP unit. Both input lengths equal `T`,
so the original left/right pairing is preserved without zip truncation.
Neither an output shape nor output reconstruction is a premise. -/
theorem source_matmul_unit_output_reconstruct
    (D T B H Q K M u : Nat) (x y z : Tensor) (xs ys outputs : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B) (hH : 0 < H)
    (hQ : 0 < Q) (hK : 0 < K) (hM : 0 < M) (hu : u < D)
    (hx : x.shape = [B * D, H * T, Q, K])
    (hy : y.shape = [B * D, H * T, K, M])
    (hxsLen : xs.length = T) (hysLen : ys.length = T)
    (hxs : ∀ a ∈ xs, a.shape = [B, H, Q, K])
    (hys : ∀ b ∈ ys, b.shape = [B, H, K, M])
    (hpreX : chunkPrimDimN 0 D u x = allGatherPrimDimN 1 T 0 xs)
    (hpreY : chunkPrimDimN 0 D u y = allGatherPrimDimN 1 T 0 ys)
    (hglobal : z = fw_matmul x y)
    (hlocal : outputs = List.zipWith fw_matmul xs ys) :
    z.shape = [B * D, H * T, Q, M] ∧
      (∀ out ∈ outputs, out.shape = [B, H, Q, M]) ∧
      chunkPrimDimN 0 D u z = allGatherPrimDimN 1 T 0 outputs := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact fw_matmul_rank4_shape x y (B * D) (H * T) Q K M hx hy
  · intro out hout
    rw [hlocal] at hout
    obtain ⟨r, hrz, rfl⟩ := List.mem_iff_getElem.mp hout
    have hrx : r < xs.length := by
      rw [List.length_zipWith] at hrz
      omega
    have hry : r < ys.length := by
      rw [List.length_zipWith] at hrz
      omega
    rw [List.getElem_zipWith]
    exact fw_matmul_rank4_shape _ _ B H Q K M
      (hxs _ (List.getElem_mem hrx)) (hys _ (List.getElem_mem hry))
  · rw [hglobal, hlocal]
    rw [fw_matmul_batch_chunk_dim0_rank4 D u B (H * T) Q K M x y
      hD hB (Nat.mul_pos hH hT) hQ hK hM hu hx hy, hpreX, hpreY]
    exact fw_matmul_allGatherPrimDimN_dim1_aligned_K_rank4
      xs ys T B H Q K M hT hH hQ hK hM hxsLen hysLen hxs hys

#print axioms fw_matmul_batch_chunk_dim0_rank4
#print axioms source_matmul_unit_output_reconstruct

end TrainVerify.Denote
