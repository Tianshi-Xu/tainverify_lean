import denote.KRankTranspose

/-!
# Source transpose12 within one DP unit

Batch-DP chunking commutes with the actual rank-4 transpose coordinate map.
The inner- and sequence-shard adapters retain the original ordered TP list and
require only input reconstruction and individual actual producer equations.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

private theorem source_transpose12_shape
    (x : Tensor) (B S H C : Nat) (hx : x.shape = [B, S, H, C]) :
    (transposeAxes 1 2 x).shape = [B, H, S, C] := by
  change listSwapAt x.shape 1 2 = [B, H, S, C]
  rw [hx]
  rfl

-- Expose the bounded contiguous read of the existing chunk operator.
private theorem source_transpose12_chunk0_flat
    (D u B stride : Nat) (x : Tensor)
    (hD : 0 < D) (hu : u < D) (hstride : 0 < stride)
    (hsize : x.shape.getD 0 0 = B * D)
    (hpost : (x.shape.drop 1).foldl (· * ·) 1 = stride)
    (idx : Nat) (hi : idx < B * stride)
    (hbound : idx < prodShape (chunkPrimDimN 0 D u x).shape) :
    valAt (chunkPrimDimN 0 D u x) idx =
      valAt x (u * (B * stride) + idx) := by
  have hnonzero : B * stride ≠ 0 := by omega
  rw [valAt_of_lt _ _ hbound]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hsize, hpost, hD.ne', ite_false,
    Nat.mul_div_cancel B hD, Nat.mod_eq_of_lt hu, hstride.ne', hnonzero]
  rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi,
    Nat.zero_mul, Nat.zero_add]
  congr 1
  calc
    (u * B + idx / stride) * stride + idx % stride =
        u * (B * stride) + (stride * (idx / stride) + idx % stride) := by ring
    _ = u * (B * stride) + idx := by rw [Nat.div_add_mod]

/-- A bounded batch-DP chunk commutes with the actual axes-1/2 transpose. -/
theorem transposeAxes_1_2_batch_chunk_dim0
    (D u B S H C : Nat) (fullx : Tensor)
    (hD : 0 < D) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H, C]) :
    chunkPrimDimN 0 D u (transposeAxes 1 2 fullx) =
      transposeAxes 1 2 (chunkPrimDimN 0 D u fullx) := by
  have hglobal := source_transpose12_shape fullx (B * D) S H C hfullx
  have hlocal : (chunkPrimDimN 0 D u fullx).shape = [B, S, H, C] := by
    rw [chunkPrimDimN_shape 0 D u fullx _ hfullx hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hleft : (chunkPrimDimN 0 D u (transposeAxes 1 2 fullx)).shape =
      [B, H, S, C] := by
    rw [chunkPrimDimN_shape 0 D u _ _ hglobal hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hright := source_transpose12_shape (chunkPrimDimN 0 D u fullx)
    B S H C hlocal
  have hW : 0 < H * S * C := Nat.mul_pos (Nat.mul_pos hH hS) hC
  have hV : 0 < S * H * C := Nat.mul_pos (Nat.mul_pos hS hH) hC
  apply Tensor.ext (by rw [hleft, hright])
  intro idx hidx
  have hi : idx < B * H * S * C := by
    rw [hleft] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  have hiBlock : idx < B * (H * S * C) := by
    simpa only [Nat.mul_assoc] using hi
  let src := idx / (H * S * C) * (S * H * C)
    + idx % (H * S * C) % (S * C) / C * (H * C)
    + idx % (H * S * C) / (S * C) * C
    + idx % (H * S * C) % (S * C) % C
  have hsrc : src < B * S * H * C :=
    transpose12_index_lt B S H C idx hS.ne' hH.ne' hC.ne' hi
  have hsrcBlock : src < B * (S * H * C) := by
    simpa only [Nat.mul_assoc] using hsrc
  have hsrcBound : src < prodShape (chunkPrimDimN 0 D u fullx).shape := by
    rw [hlocal]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hsrc
  have hshiftBound : u * (B * (H * S * C)) + idx < (B * D) * H * S * C := by
    calc
      u * (B * (H * S * C)) + idx <
          u * (B * (H * S * C)) + B * (H * S * C) :=
        Nat.add_lt_add_left hiBlock _
      _ = (u + 1) * (B * (H * S * C)) := by ring
      _ ≤ D * (B * (H * S * C)) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hu)
      _ = (B * D) * H * S * C := by ring
  have hleftRead := source_transpose12_chunk0_flat D u B (H * S * C)
    (transposeAxes 1 2 fullx) hD hu hW
    (by rw [hglobal]; rfl)
    (by simp only [hglobal, List.drop, List.foldl, Nat.one_mul, Nat.mul_assoc])
    idx hiBlock hidx
  have hinputRead := source_transpose12_chunk0_flat D u B (S * H * C)
    fullx hD hu hV (by rw [hfullx]; rfl)
    (by simp only [hfullx, List.drop, List.foldl, Nat.one_mul, Nat.mul_assoc])
    src hsrcBlock hsrcBound
  have hshiftDiv : (u * (B * (H * S * C)) + idx) / (H * S * C) =
      u * B + idx / (H * S * C) := by
    rw [show u * (B * (H * S * C)) = (H * S * C) * (u * B) by ring,
      Nat.mul_add_div hW]
  have hshiftMod : (u * (B * (H * S * C)) + idx) % (H * S * C) =
      idx % (H * S * C) := by
    rw [show u * (B * (H * S * C)) = (H * S * C) * (u * B) by ring,
      Nat.mul_add_mod_self_left]
  rw [hleftRead,
    transposeAxes_1_2_valAt_gen fullx (B * D) S H C _ hfullx
      hS.ne' hH.ne' hC.ne' hshiftBound,
    transposeAxes_1_2_valAt_gen (chunkPrimDimN 0 D u fullx) B S H C idx hlocal
      hS.ne' hH.ne' hC.ne' hi,
    hinputRead]
  congr 1
  simp only [hshiftDiv, hshiftMod]
  dsimp [src]
  ring

-- The induction motive contains only the pointwise producer relation.
private theorem source_transpose12_outputs_eq_map {xs ys : List Tensor}
    (hlocal : List.Forall₂ (fun x y => y = transposeAxes 1 2 x) xs ys) :
    ys = xs.map (transposeAxes 1 2) := by
  induction hlocal with
  | nil => rfl
  | cons hxy hrest ih => exact congrArg₂ List.cons hxy ih

/-- Inner shards stay on axis 3 after transpose12, within the selected DP unit. -/
theorem source_transpose12_inner_unit_output_reconstruct
    (D T B S H C u : Nat) (fullx globaly : Tensor) (xs ys : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H, C * T])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, H, C])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 3 T 0 xs)
    (hglobal : globaly = transposeAxes 1 2 fullx)
    (hlocal : List.Forall₂ (fun x y => y = transposeAxes 1 2 x) xs ys) :
    globaly.shape = [B * D, H, S, C * T] ∧
      (∀ y ∈ ys, y.shape = [B, H, S, C]) ∧
      chunkPrimDimN 0 D u globaly = allGatherPrimDimN 3 T 0 ys := by
  have houts := source_transpose12_outputs_eq_map hlocal
  have hne : xs ≠ [] := by
    intro hempty
    have hz : xs.length = 0 := by rw [hempty]; rfl
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact source_transpose12_shape fullx (B * D) S H (C * T) hfullx
  · intro y hy
    rw [houts] at hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact source_transpose12_shape x B S H C (hshapes x hx)
  · rw [hglobal, houts,
      transposeAxes_1_2_batch_chunk_dim0 D u B S H (C * T) fullx
        hD hB hS hH (Nat.mul_pos hC hT) hu hfullx, hpre]
    have htp := transposeAxes_1_2_allGather_dim3_rank4 xs B S H C hne hshapes
    rw [hlen] at htp
    exact htp

/-- Sequence shards move from axis 1 to axis 2 after transpose12. -/
theorem source_transpose12_sequence_unit_output_reconstruct
    (D T B S H C u : Nat) (fullx globaly : Tensor) (xs ys : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S * T, H, C])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, H, C])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 1 T 0 xs)
    (hglobal : globaly = transposeAxes 1 2 fullx)
    (hlocal : List.Forall₂ (fun x y => y = transposeAxes 1 2 x) xs ys) :
    globaly.shape = [B * D, H, S * T, C] ∧
      (∀ y ∈ ys, y.shape = [B, H, S, C]) ∧
      chunkPrimDimN 0 D u globaly = allGatherPrimDimN 2 T 0 ys := by
  have houts := source_transpose12_outputs_eq_map hlocal
  have hne : xs ≠ [] := by
    intro hempty
    have hz : xs.length = 0 := by rw [hempty]; rfl
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact source_transpose12_shape fullx (B * D) (S * T) H C hfullx
  · intro y hy
    rw [houts] at hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact source_transpose12_shape x B S H C (hshapes x hx)
  · rw [hglobal, houts,
      transposeAxes_1_2_batch_chunk_dim0 D u B (S * T) H C fullx
        hD hB (Nat.mul_pos hS hT) hH hC hu hfullx, hpre]
    have htp := transposeAxes_1_2_allGather_dim1_to_dim2_rank4
      xs B S H C hne hshapes
    rw [hlen] at htp
    exact htp

#print axioms transposeAxes_1_2_batch_chunk_dim0
#print axioms source_transpose12_inner_unit_output_reconstruct
#print axioms source_transpose12_sequence_unit_output_reconstruct

end
end TrainVerify.Denote
