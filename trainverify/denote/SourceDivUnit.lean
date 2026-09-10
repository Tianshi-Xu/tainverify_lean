import denote.KRankDivGather

/-!
# Rank-4 scalar division within one DP unit

Contiguous batch chunks commute with scalar division, and ordered axis-3
shards reconstruct using the existing division/gather theorem. The same
`c : Scalar` is used in the global and local executions, including `c = 0`
under the original total Denote scalar semantics. Only predecessor shapes,
predecessor reconstruction, and actual producer equations are premises.
This is tensor algebra, not runtime refinement or source-ownership evidence.
-/

namespace TrainVerify.Denote

set_option maxHeartbeats 500000

private theorem source_div_chunk_shape
    (D u B H Q K : Nat) (x : Tensor)
    (hD : 0 < D) (hx : x.shape = [B * D, H, Q, K]) :
    (chunkPrimDimN 0 D u x).shape = [B, H, Q, K] := by
  rw [chunkPrimDimN_shape 0 D u x _ hx hD.ne']
  simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]

private theorem source_div_chunk0_flat
    (D u B H Q K : Nat) (x : Tensor)
    (hx : x.shape = [B * D, H, Q, K])
    (hD : 0 < D) (hu : u < D)
    (hH : 0 < H) (hQ : 0 < Q) (hK : 0 < K)
    (idx : Nat) (hi : idx < B * H * Q * K) :
    valAt (chunkPrimDimN 0 D u x) idx =
      valAt x (u * (B * H * Q * K) + idx) := by
  have hdiv : B * D / D = B := Nat.mul_div_cancel B hD
  have hshape := source_div_chunk_shape D u B H Q K x hD hx
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

/-- Scalar division commutes with a legal contiguous batch chunk of a rank-4
score tensor whose complete axis-3 extent is `C * T`. -/
theorem fw_div_batch_chunk_dim0_rank4
    (c : Scalar) (D u B H Q C T : Nat) (full : Tensor)
    (hD : 0 < D) (hH : 0 < H) (hQ : 0 < Q)
    (hC : 0 < C) (hT : 0 < T) (hu : u < D)
    (hfull : full.shape = [B * D, H, Q, C * T]) :
    chunkPrimDimN 0 D u (fw_div c full) =
      fw_div c (chunkPrimDimN 0 D u full) := by
  have hCT : 0 < C * T := Nat.mul_pos hC hT
  have hglobal : (fw_div c full).shape = [B * D, H, Q, C * T] :=
    (fw_div_shape_g92 c full).trans hfull
  have hchunk := source_div_chunk_shape D u B H Q (C * T) full hD hfull
  have hleft := source_div_chunk_shape D u B H Q (C * T) (fw_div c full) hD hglobal
  apply Tensor.ext (by rw [hleft, fw_div_shape_g92, hchunk])
  intro idx hidx
  have hbound : idx < B * H * Q * (C * T) := by
    rw [hleft] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  have hlocalBound : idx < prodShape (chunkPrimDimN 0 D u full).shape := by
    rw [hchunk]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hbound
  have hfullBound : u * (B * H * Q * (C * T)) + idx < prodShape full.shape := by
    have h : u * (B * H * Q * (C * T)) + idx < D * (B * H * Q * (C * T)) := by
      calc
        u * (B * H * Q * (C * T)) + idx <
            u * (B * H * Q * (C * T)) + (B * H * Q * (C * T)) :=
          Nat.add_lt_add_left hbound _
        _ = (u + 1) * (B * H * Q * (C * T)) := by ring
        _ ≤ D * (B * H * Q * (C * T)) := Nat.mul_le_mul_right _ hu
    rw [hfull]
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  rw [source_div_chunk0_flat D u B H Q (C * T) (fw_div c full)
    hglobal hD hu hH hQ hCT idx hbound]
  rw [fw_div_valAt_g92 c full _ hfullBound,
    fw_div_valAt_g92 c (chunkPrimDimN 0 D u full) idx hlocalBound,
    source_div_chunk0_flat D u B H Q (C * T) full
      hfull hD hu hH hQ hCT idx hbound]

/-- Actual global and ordered local division executions inherit complete
output shapes and reconstruct within the selected DP unit. Output shape
and output reconstruction are conclusions, not additional premises. -/
theorem source_div_unit_output_reconstruct
    (c : Scalar) (D T B H Q C u : Nat)
    (full globalout : Tensor) (xs outputs : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hH : 0 < H)
    (hQ : 0 < Q) (hC : 0 < C) (hu : u < D)
    (hfull : full.shape = [B * D, H, Q, C * T])
    (hxsLen : xs.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, H, Q, C])
    (hpre : chunkPrimDimN 0 D u full = allGatherPrimDimN 3 T 0 xs)
    (hglobal : globalout = fw_div c full)
    (hlocal : outputs = xs.map (fw_div c)) :
    globalout.shape = [B * D, H, Q, C * T] ∧
      (∀ out ∈ outputs, out.shape = [B, H, Q, C]) ∧
      chunkPrimDimN 0 D u globalout = allGatherPrimDimN 3 T 0 outputs := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal, fw_div_shape_g92, hfull]
  · intro out hout
    rw [hlocal] at hout
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hout
    rw [fw_div_shape_g92, hxs x hx]
  · rw [hglobal, hlocal]
    rw [fw_div_batch_chunk_dim0_rank4 c D u B H Q C T full
      hD hH hQ hC hT hu hfull, hpre]
    have hne : xs ≠ [] := by
      intro hempty
      rw [hempty] at hxsLen
      simp only [List.length_nil] at hxsLen
      omega
    have hgather := fw_div_allGatherPrimDimN_dim3_rank4 c xs B H Q C hne hxs
    rw [hxsLen] at hgather
    exact hgather

#print axioms fw_div_batch_chunk_dim0_rank4
#print axioms source_div_unit_output_reconstruct

end TrainVerify.Denote
