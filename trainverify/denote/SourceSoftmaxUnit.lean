import denote.KRankSoftmaxGather

/-!
# Last-axis softmax within one DP unit

Batch chunking selects complete normalization rows; ordered TP shards split
heads (axis 1), never the normalized last axis. The original zero-expSum
conditional is retained. The adapter assumes predecessor reconstruction and
actual producer equations, and derives all output shapes and reconstruction.
This is tensor algebra, not runtime refinement or source-ownership evidence.
-/

namespace TrainVerify.Denote

open scoped BigOperators

set_option maxHeartbeats 500000

private theorem source_softmax_chunk_shape
    (D u B H Q C : Nat) (x : Tensor)
    (hD : 0 < D) (hx : x.shape = [B * D, H, Q, C]) :
    (chunkPrimDimN 0 D u x).shape = [B, H, Q, C] := by
  rw [chunkPrimDimN_shape 0 D u x _ hx hD.ne']
  simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]

private theorem source_softmax_chunk0_flat
    (D u B H Q C : Nat) (x : Tensor)
    (hx : x.shape = [B * D, H, Q, C])
    (hD : 0 < D) (hu : u < D)
    (hH : 0 < H) (hQ : 0 < Q) (hC : 0 < C)
    (idx : Nat) (hi : idx < B * H * Q * C) :
    valAt (chunkPrimDimN 0 D u x) idx =
      valAt x (u * (B * H * Q * C) + idx) := by
  have hdiv : B * D / D = B := Nat.mul_div_cancel B hD
  have hshape := source_softmax_chunk_shape D u B H Q C x hD hx
  have hbound : idx < prodShape (chunkPrimDimN 0 D u x).shape := by
    rw [hshape]
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one] using hi
  have hstride : H * Q * C ≠ 0 := (Nat.mul_pos (Nat.mul_pos hH hQ) hC).ne'
  have hlocal : idx < B * (H * Q * C) := by
    simpa only [Nat.mul_assoc] using hi
  have hnonzero : B * (H * Q * C) ≠ 0 := by omega
  rw [valAt_of_lt _ _ hbound]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hx, List.getD_cons_zero, List.drop, List.foldl,
    Nat.one_mul, Nat.mul_one, hD.ne', ite_false, hdiv, Nat.mod_eq_of_lt hu,
    hstride, hnonzero]
  rw [Nat.div_eq_of_lt hlocal, Nat.mod_eq_of_lt hlocal,
    Nat.zero_mul, Nat.zero_add]
  congr 1
  calc
    (u * B + idx / (H * Q * C)) * (H * Q * C) + idx % (H * Q * C) =
        u * (B * H * Q * C) +
          ((H * Q * C) * (idx / (H * Q * C)) + idx % (H * Q * C)) := by ring
    _ = u * (B * H * Q * C) + idx := by rw [Nat.div_add_mod]

/-- Last-axis softmax commutes with a legal contiguous batch chunk of a
rank-4 tensor. The normalized axis remains complete in every chunk. -/
theorem fw_softmax_batch_chunk_dim0_rank4
    (D u B H Q C : Nat) (full : Tensor)
    (hD : 0 < D) (hH : 0 < H) (hQ : 0 < Q) (hC : 0 < C)
    (hu : u < D) (hfull : full.shape = [B * D, H, Q, C]) :
    chunkPrimDimN 0 D u (fw_softmax full) =
      fw_softmax (chunkPrimDimN 0 D u full) := by
  have hglobal : (fw_softmax full).shape = [B * D, H, Q, C] :=
    (fw_softmax_shape_g43 full).trans hfull
  have hchunk := source_softmax_chunk_shape D u B H Q C full hD hfull
  have hleft := source_softmax_chunk_shape D u B H Q C (fw_softmax full) hD hglobal
  apply Tensor.ext (by rw [hleft, fw_softmax_shape_g43, hchunk])
  intro idx hidx
  have hbound : idx < B * H * Q * C := by
    rw [hleft] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one] using hidx
  have hlocalBound : idx < prodShape (chunkPrimDimN 0 D u full).shape := by
    rw [hchunk]
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one] using hbound
  have hfullBound : u * (B * H * Q * C) + idx < prodShape full.shape := by
    have h : u * (B * H * Q * C) + idx < D * (B * H * Q * C) := by
      calc
        u * (B * H * Q * C) + idx <
            u * (B * H * Q * C) + (B * H * Q * C) :=
          Nat.add_lt_add_left hbound _
        _ = (u + 1) * (B * H * Q * C) := by ring
        _ ≤ D * (B * H * Q * C) := Nat.mul_le_mul_right _ hu
    rw [hfull]
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hrow : idx / C < B * H * Q := by
    rw [Nat.div_lt_iff_lt_mul hC]
    exact hbound
  have hrowBound : ∀ z < C, idx / C * C + z < B * H * Q * C := by
    intro z hz
    calc
      idx / C * C + z < idx / C * C + C := Nat.add_lt_add_left hz _
      _ = (idx / C + 1) * C := by ring
      _ ≤ B * H * Q * C := Nat.mul_le_mul_right C hrow
  have hglobalDiv : (u * (B * H * Q * C) + idx) / C =
      u * (B * H * Q) + idx / C := by
    rw [show u * (B * H * Q * C) + idx = C * (u * (B * H * Q)) + idx by ring]
    rw [Nat.mul_add_div hC]
  have hsum :
      (∑ z ∈ Finset.range C,
        expFn (valAt full (((u * (B * H * Q * C) + idx) / C) * C + z))) =
      ∑ z ∈ Finset.range C,
        expFn (valAt (chunkPrimDimN 0 D u full) (idx / C * C + z)) := by
    apply Finset.sum_congr rfl
    intro z hz
    have hzC : z < C := Finset.mem_range.mp hz
    rw [hglobalDiv]
    rw [show (u * (B * H * Q) + idx / C) * C + z =
      u * (B * H * Q * C) + (idx / C * C + z) by ring]
    rw [source_softmax_chunk0_flat D u B H Q C full hfull hD hu hH hQ hC
      (idx / C * C + z) (hrowBound z hzC)]
  rw [source_softmax_chunk0_flat D u B H Q C (fw_softmax full)
    hglobal hD hu hH hQ hC idx hbound]
  rw [fw_softmax_valAt_g43 full C [Q, H, B * D]
    (by rw [hfull]; rfl) hC.ne' _ hfullBound]
  rw [fw_softmax_valAt_g43 (chunkPrimDimN 0 D u full) C [Q, H, B]
    (by rw [hchunk]; rfl) hC.ne' idx hlocalBound]
  rw [hsum, source_softmax_chunk0_flat D u B H Q C full
    hfull hD hu hH hQ hC idx hbound]

/-- Actual global and ordered head-sharded local softmax executions inherit
both global and every local output shape and reconstruct in the chosen DP
unit. Only predecessor reconstruction is assumed; axis 3 is unsharded. -/
theorem source_softmax_unit_output_reconstruct
    (D T B H Q C u : Nat)
    (full globalout : Tensor) (xs outputs : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hH : 0 < H)
    (hQ : 0 < Q) (hC : 0 < C) (hu : u < D)
    (hfull : full.shape = [B * D, H * T, Q, C])
    (hxsLen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, H, Q, C])
    (hpre : chunkPrimDimN 0 D u full = allGatherPrimDimN 1 T 0 xs)
    (hglobal : globalout = fw_softmax full)
    (hlocal : outputs = xs.map fw_softmax) :
    globalout.shape = [B * D, H * T, Q, C] ∧
      (∀ out ∈ outputs, out.shape = [B, H, Q, C]) ∧
      chunkPrimDimN 0 D u globalout = allGatherPrimDimN 1 T 0 outputs := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal, fw_softmax_shape_g43, hfull]
  · intro out hout
    rw [hlocal] at hout
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hout
    rw [fw_softmax_shape_g43, hxs x hx]
  · rw [hglobal, hlocal]
    rw [fw_softmax_batch_chunk_dim0_rank4 D u B (H * T) Q C full
      hD (Nat.mul_pos hH hT) hQ hC hu hfull, hpre]
    have hne : xs ≠ [] := by
      intro hempty
      rw [hempty] at hxsLen
      simp only [List.length_nil] at hxsLen
      omega
    have hgather := fw_softmax_allGatherPrimDimN_dim1_rank4 xs B H Q C hne hC hxs
    rw [hxsLen] at hgather
    exact hgather

#print axioms fw_softmax_batch_chunk_dim0_rank4
#print axioms source_softmax_unit_output_reconstruct

end TrainVerify.Denote
