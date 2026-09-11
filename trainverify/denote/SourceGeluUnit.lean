import denote.Denote

/-!
Exact GELU within a DP unit: a legal batch chunk and ordered sequence shards
preserve elementwise scalar evaluation. The full output shape, every local
output shape and reconstruction are conclusions from predecessor facts and
individual source executions. No analytic approximation or output hypothesis.
-/
namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

private theorem source_gelu_chunk_shape
    (D u B S H : Nat) (x : Tensor)
    (hD : 0 < D) (hx : x.shape = [B * D, S, H]) :
    (chunkPrimDimN 0 D u x).shape = [B, S, H] := by
  rw [chunkPrimDimN_shape 0 D u x _ hx hD.ne']
  simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]

-- The public dim0 coordinate lemma covers matrices. Existing 3D flat-read
-- helpers in Denote and SourceEmbeddingBatch are private, so keep the small
-- missing bounded read here, without importing fixed-shape axioms.
private theorem source_gelu_chunk0_flat
    (D u B S H : Nat) (x : Tensor)
    (hx : x.shape = [B * D, S, H]) (hD : 0 < D) (hu : u < D)
    (hS : 0 < S) (hH : 0 < H)
    (idx : Nat) (hi : idx < B * S * H) :
    valAt (chunkPrimDimN 0 D u x) idx =
      valAt x (u * (B * S * H) + idx) := by
  have hdiv : B * D / D = B := Nat.mul_div_cancel B hD
  have hshape := source_gelu_chunk_shape D u B S H x hD hx
  have hbound : idx < prodShape (chunkPrimDimN 0 D u x).shape := by
    rw [hshape]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  have hstride : S * H ≠ 0 := (Nat.mul_pos hS hH).ne'
  have hlocal : idx < B * (S * H) := by
    simpa only [Nat.mul_assoc] using hi
  have hnonzero : B * (S * H) ≠ 0 := by omega
  rw [valAt_of_lt _ _ hbound]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hx, List.getD_cons_zero, List.drop, List.foldl,
    Nat.one_mul, hD.ne', ite_false, hdiv, Nat.mod_eq_of_lt hu,
    hstride, hnonzero]
  rw [Nat.div_eq_of_lt hlocal, Nat.mod_eq_of_lt hlocal,
    Nat.zero_mul, Nat.zero_add]
  congr 1
  calc
    (u * B + idx / (S * H)) * (S * H) + idx % (S * H) =
        u * (B * S * H) + ((S * H) * (idx / (S * H)) + idx % (S * H)) := by ring
    _ = u * (B * S * H) + idx := by rw [Nat.div_add_mod]

/-- Exact GELU commutes with a legal contiguous DP batch chunk. -/
theorem fw_gelu_batch_chunk_dim0
    (D u B S H : Nat) (fullx : Tensor)
    (hD : 0 < D) (_hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H]) :
    chunkPrimDimN 0 D u (fw_gelu fullx) =
      fw_gelu (chunkPrimDimN 0 D u fullx) := by
  have hlocal := source_gelu_chunk_shape D u B S H fullx hD hfullx
  have hglobal : (fw_gelu fullx).shape = [B * D, S, H] :=
    (fw_gelu_shape fullx).trans hfullx
  have hleft := source_gelu_chunk_shape D u B S H (fw_gelu fullx) hD hglobal
  have hright : (fw_gelu (chunkPrimDimN 0 D u fullx)).shape = [B,S,H] :=
    (fw_gelu_shape _).trans hlocal
  apply Tensor.ext (by rw [hleft, hright])
  intro idx hidx
  have hi : idx < B * S * H := by
    rw [hleft] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  have hchunkIdx : idx < prodShape (chunkPrimDimN 0 D u fullx).shape := by
    rw [hlocal]
    simpa only [prodShape, List.foldl, Nat.one_mul] using hi
  have hfullIdx : u * (B * S * H) + idx < prodShape fullx.shape := by
    rw [hfullx]
    simp only [prodShape, List.foldl, Nat.one_mul]
    calc
      u * (B * S * H) + idx < u * (B * S * H) + B * S * H := Nat.add_lt_add_left hi _
      _ = (u + 1) * (B * S * H) := by ring
      _ ≤ D * (B * S * H) := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hu)
      _ = B * D * S * H := by ring
  rw [source_gelu_chunk0_flat D u B S H (fw_gelu fullx) hglobal hD hu hS hH idx hi,
      fw_gelu_valAt fullx _ hfullIdx, fw_gelu_valAt _ idx hchunkIdx,
      source_gelu_chunk0_flat D u B S H fullx hfullx hD hu hS hH idx hi]

/-- Complete sequence shards reconstruct GELU in each DP batch slice. -/
theorem source_gelu_unit_reconstruct
    (D T B S H u : Nat) (fullx : Tensor) (xs : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S * T, H])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B,S,H])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 1 T 0 xs) :
    chunkPrimDimN 0 D u (fw_gelu fullx) = allGatherPrimDimN 1 T 0 (xs.map fw_gelu) := by
  rw [fw_gelu_batch_chunk_dim0 D u B (S*T) H fullx hD hB (Nat.mul_pos hS hT) hH hu hfullx, hpre]
  apply fw_gelu_allGatherPrimDimN_eq 1 T xs [B,S,H] hT hlen
  · cases xs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons x rest => exact hshapes x List.mem_cons_self
  · intro i hi
    exact hshapes _ (List.get_mem _ ⟨i,hi⟩)

/-- Individual source reads yield all three output obligations, not only values. -/
theorem source_gelu_unit_output_reconstruct
    (D T B S H u : Nat) (fullx globalOut : Tensor) (xs localOuts : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S * T, H])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B,S,H])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 1 T 0 xs)
    (hglobal : globalOut = fw_gelu fullx)
    (hlocal : List.Forall₂ (fun x y => y = fw_gelu x) xs localOuts) :
    globalOut.shape = [B * D, S * T, H] ∧
      (∀ y ∈ localOuts, y.shape = [B,S,H]) ∧
      chunkPrimDimN 0 D u globalOut = allGatherPrimDimN 1 T 0 localOuts := by
  have transport : ∀ {ins outs : List Tensor},
      List.Forall₂ (fun x y => y = fw_gelu x) ins outs → outs = ins.map fw_gelu := by
    intro ins outs heq
    induction heq with
    | nil => rfl
    | cons hxy hrest ih => exact congrArg₂ List.cons hxy ih
  have houts : localOuts = xs.map fw_gelu := transport hlocal
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal, fw_gelu_shape]
    exact hfullx
  · intro y hy
    rw [houts] at hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact (fw_gelu_shape x).trans (hshapes x hx)
  · rw [hglobal, houts]
    exact source_gelu_unit_reconstruct D T B S H u fullx xs hD hT hB hS hH hu hfullx hlen hshapes hpre

#print axioms TrainVerify.Denote.fw_gelu_batch_chunk_dim0
#print axioms TrainVerify.Denote.source_gelu_unit_reconstruct
#print axioms TrainVerify.Denote.source_gelu_unit_output_reconstruct
end
end TrainVerify.Denote
