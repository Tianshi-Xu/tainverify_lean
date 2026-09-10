import denote.KRankTranspose23Extra

/-!
# Source transpose23 within one DP unit

Batch chunking commutes with the actual bounded rank-4 transpose coordinate map.
Inner TP shards move from axis 3 to axis 2; the adapter consumes only input
reconstruction and actual global/local producer equations.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

private theorem source_transpose23_shape
    (x : Tensor) (B S H C : Nat) (hx : x.shape = [B, S, H, C]) :
    (transposeAxes 2 3 x).shape = [B, S, C, H] := by
  change listSwapAt x.shape 2 3 = [B, S, C, H]
  rw [hx]
  rfl

-- Bounded contiguous batch read, directly from the chunk operator.
private theorem source_transpose23_chunk0_flat
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

private theorem source_transpose23_append_lt
    (a A b K : Nat) (ha : a < A) (hb : b < K) :
    a * K + b < A * K := by
  calc
    a * K + b < a * K + K := Nat.add_lt_add_left hb _
    _ = (a + 1) * K := by ring
    _ ≤ A * K := Nat.mul_le_mul_right K (Nat.succ_le_iff.mpr ha)

/-- A bounded batch-DP chunk commutes with the actual axes-2/3 transpose. -/
theorem transposeAxes_2_3_batch_chunk_dim0
    (D u B S H C : Nat) (fullx : Tensor)
    (hD : 0 < D) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H, C]) :
    chunkPrimDimN 0 D u (transposeAxes 2 3 fullx) =
      transposeAxes 2 3 (chunkPrimDimN 0 D u fullx) := by
  have hglobal := source_transpose23_shape fullx (B * D) S H C hfullx
  have hlocal : (chunkPrimDimN 0 D u fullx).shape = [B, S, H, C] := by
    rw [chunkPrimDimN_shape 0 D u fullx _ hfullx hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hleft : (chunkPrimDimN 0 D u (transposeAxes 2 3 fullx)).shape =
      [B, S, C, H] := by
    rw [chunkPrimDimN_shape 0 D u _ _ hglobal hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hright := source_transpose23_shape (chunkPrimDimN 0 D u fullx)
    B S H C hlocal
  have hW : 0 < S * C * H := Nat.mul_pos (Nat.mul_pos hS hC) hH
  have hV : 0 < S * H * C := Nat.mul_pos (Nat.mul_pos hS hH) hC
  apply Tensor.ext (by rw [hleft, hright])
  intro idx hidx
  have hi : idx < B * S * C * H := by
    rw [hleft] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  have hiBlock : idx < B * (S * C * H) := by
    simpa only [Nat.mul_assoc] using hi
  let a := idx / (S * C * H)
  let b := idx % (S * C * H) / (C * H)
  let p := idx % (S * C * H) % (C * H) % H
  let q := idx % (S * C * H) % (C * H) / H
  let src := a * (S * C * H) + b * (C * H) + p * C + q
  have ha : a < B := by
    apply Nat.div_lt_of_lt_mul
    simpa only [Nat.mul_comm] using hiBlock
  have hb : b < S := by
    apply Nat.div_lt_of_lt_mul
    have hr := Nat.mod_lt idx hW
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hr
  have hp : p < H := Nat.mod_lt _ hH
  have hq : q < C := by
    apply Nat.div_lt_of_lt_mul
    have hr := Nat.mod_lt (idx % (S * C * H)) (Nat.mul_pos hC hH)
    simpa only [Nat.mul_comm] using hr
  have hinner := source_transpose23_append_lt p H q C hp hq
  have hseq := source_transpose23_append_lt b S (p * C + q) (H * C) hb hinner
  have hbatch := source_transpose23_append_lt a B
    (b * (H * C) + (p * C + q)) (S * (H * C)) ha hseq
  have hsrcBlock : src < B * (S * H * C) := by
    calc
      src = a * (S * (H * C)) + (b * (H * C) + (p * C + q)) := by
        dsimp [src]
        ring
      _ < B * (S * (H * C)) := hbatch
      _ = B * (S * H * C) := by ring
  have hsrcBound : src < prodShape (chunkPrimDimN 0 D u fullx).shape := by
    rw [hlocal]
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hsrcBlock
  have hshiftBound : u * (B * (S * C * H)) + idx < (B * D) * S * C * H := by
    calc
      u * (B * (S * C * H)) + idx <
          u * (B * (S * C * H)) + B * (S * C * H) :=
        Nat.add_lt_add_left hiBlock _
      _ = (u + 1) * (B * (S * C * H)) := by ring
      _ ≤ D * (B * (S * C * H)) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hu)
      _ = (B * D) * S * C * H := by ring
  have hleftRead := source_transpose23_chunk0_flat D u B (S * C * H)
    (transposeAxes 2 3 fullx) hD hu hW
    (by rw [hglobal]; rfl)
    (by simp only [hglobal, List.drop, List.foldl, Nat.one_mul, Nat.mul_assoc])
    idx hiBlock hidx
  have hinputRead := source_transpose23_chunk0_flat D u B (S * H * C)
    fullx hD hu hV (by rw [hfullx]; rfl)
    (by simp only [hfullx, List.drop, List.foldl, Nat.one_mul, Nat.mul_assoc])
    src hsrcBlock hsrcBound
  have hshiftDiv : (u * (B * (S * C * H)) + idx) / (S * C * H) =
      u * B + idx / (S * C * H) := by
    rw [show u * (B * (S * C * H)) = (S * C * H) * (u * B) by ring,
      Nat.mul_add_div hW]
  have hshiftMod : (u * (B * (S * C * H)) + idx) % (S * C * H) =
      idx % (S * C * H) := by
    rw [show u * (B * (S * C * H)) = (S * C * H) * (u * B) by ring,
      Nat.mul_add_mod_self_left]
  rw [hleftRead,
    transposeAxes_2_3_valAt_gen fullx (B * D) S H C _ hfullx
      hS.ne' hH.ne' hC.ne' hshiftBound,
    transposeAxes_2_3_valAt_gen (chunkPrimDimN 0 D u fullx) B S H C idx hlocal
      hS.ne' hH.ne' hC.ne' hi,
    hinputRead]
  congr 1
  simp only [hshiftDiv, hshiftMod]
  dsimp [src, a, b, p, q]
  ring

-- Keep the induction motive independent of shapes and reconstruction goals.
private theorem source_transpose23_outputs_eq_map {xs ys : List Tensor}
    (hlocal : List.Forall₂ (fun x y => y = transposeAxes 2 3 x) xs ys) :
    ys = xs.map (transposeAxes 2 3) := by
  induction hlocal with
  | nil => rfl
  | cons hxy hrest ih => exact congrArg₂ List.cons hxy ih

/-- Inner TP shards move from axis 3 to axis 2 within the selected DP unit. -/
theorem source_transpose23_inner_unit_output_reconstruct
    (D T B S H C u : Nat) (fullx globaly : Tensor) (xs ys : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H, C * T])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, H, C])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 3 T 0 xs)
    (hglobal : globaly = transposeAxes 2 3 fullx)
    (hlocal : List.Forall₂ (fun x y => y = transposeAxes 2 3 x) xs ys) :
    globaly.shape = [B * D, S, C * T, H] ∧
      (∀ y ∈ ys, y.shape = [B, S, C, H]) ∧
      chunkPrimDimN 0 D u globaly = allGatherPrimDimN 2 T 0 ys := by
  have houts := source_transpose23_outputs_eq_map hlocal
  have hne : xs ≠ [] := by
    intro hempty
    have hz : xs.length = 0 := by rw [hempty]; rfl
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact source_transpose23_shape fullx (B * D) S H (C * T) hfullx
  · intro y hy
    rw [houts] at hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact source_transpose23_shape x B S H C (hshapes x hx)
  · rw [hglobal, houts,
      transposeAxes_2_3_batch_chunk_dim0 D u B S H (C * T) fullx
        hD hB hS hH (Nat.mul_pos hC hT) hu hfullx, hpre]
    have htp := transposeAxes_2_3_allGather_dim3_to_dim2_rank4
      xs B S H C hne hshapes
    rw [hlen] at htp
    exact htp

#print axioms transposeAxes_2_3_batch_chunk_dim0
#print axioms source_transpose23_inner_unit_output_reconstruct

end
end TrainVerify.Denote
