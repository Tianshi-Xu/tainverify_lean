import denote.KRankLayernormGather

/-!
# Source LayerNorm within one DP unit

Batch chunks and sequence gathers preserve each complete hidden-axis row.
Only predecessor reconstruction and individual source executions are premises;
output reconstruction is a conclusion. The mean, variance, sqrt, epsilon,
and weight/bias order are those of `fw_layernorm` without approximation.

Static candidate: kernel compilation and axiom auditing belong to the parent's
serial validation lane.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

private theorem source_layernorm_shape (x gamma beta : Tensor) :
    (fw_layernorm x gamma beta).shape = x.shape := by
  unfold fw_layernorm
  split <;> rfl

private theorem source_layernorm_chunk_shape
    (D u B S H : Nat) (x : Tensor)
    (hD : 0 < D) (hx : x.shape = [B * D, S, H]) :
    (chunkPrimDimN 0 D u x).shape = [B, S, H] := by
  rw [chunkPrimDimN_shape 0 D u x _ hx hD.ne']
  simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]

-- The public dim0 coordinate lemma covers matrices. Existing 3D flat-read
-- helpers in Denote and SourceEmbeddingBatch are private, so keep the small
-- missing bounded read here, without importing fixed-shape axioms.
private theorem source_layernorm_chunk0_flat
    (D u B S H : Nat) (x : Tensor)
    (hx : x.shape = [B * D, S, H]) (hD : 0 < D) (hu : u < D)
    (hS : 0 < S) (hH : 0 < H)
    (idx : Nat) (hi : idx < B * S * H) :
    valAt (chunkPrimDimN 0 D u x) idx =
      valAt x (u * (B * S * H) + idx) := by
  have hdiv : B * D / D = B := Nat.mul_div_cancel B hD
  have hshape := source_layernorm_chunk_shape D u B S H x hD hx
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

/-- Last-axis LayerNorm commutes with a legal contiguous DP batch chunk.
The shared parameters retain the full hidden width `[H]`. -/
theorem fw_layernorm_batch_chunk_dim0
    (D u B S H : Nat) (fullx gamma beta : Tensor)
    (hD : 0 < D) (_hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H])
    (_hgamma : gamma.shape = [H]) (_hbeta : beta.shape = [H]) :
    chunkPrimDimN 0 D u (fw_layernorm fullx gamma beta) =
      fw_layernorm (chunkPrimDimN 0 D u fullx) gamma beta := by
  have hlocal := source_layernorm_chunk_shape D u B S H fullx hD hfullx
  have hglobal : (fw_layernorm fullx gamma beta).shape = [B * D, S, H] :=
    (source_layernorm_shape fullx gamma beta).trans hfullx
  have hleft := source_layernorm_chunk_shape D u B S H
    (fw_layernorm fullx gamma beta) hD hglobal
  have hright :
      (fw_layernorm (chunkPrimDimN 0 D u fullx) gamma beta).shape = [B, S, H] :=
    (source_layernorm_shape _ gamma beta).trans hlocal
  apply Tensor.ext (by rw [hleft, hright])
  intro idx hidx
  have hi : idx < B * S * H := by
    rw [hleft] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  let row := idx / H
  let q := row / S
  let p := row % S
  let j := idx % H
  have hj : j < H := Nat.mod_lt _ hH
  have hp : p < S := Nat.mod_lt _ hS
  have hrow : row < B * S := by
    dsimp only [row]
    rw [Nat.div_lt_iff_lt_mul hH]
    exact hi
  have hq : q < B := by
    dsimp only [q]
    rw [Nat.div_lt_iff_lt_mul hS]
    exact hrow
  have hrEq : q * S + p = row := by
    dsimp only [q, p]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod row S
  have hiEq : (q * S + p) * H + j = idx := by
    rw [hrEq]
    dsimp only [row, j]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod idx H
  have hqfull : u * B + q < B * D := by
    calc
      u * B + q < u * B + B := Nat.add_lt_add_left hq _
      _ = (u + 1) * B := by ring
      _ ≤ D * B := Nat.mul_le_mul_right B (Nat.succ_le_iff.mpr hu)
      _ = B * D := Nat.mul_comm _ _
  have hread : ∀ k < H,
      valAt (chunkPrimDimN 0 D u fullx) ((q * S + p) * H + k) =
        valAt fullx (((u * B + q) * S + p) * H + k) := by
    intro k hk
    have hbnd : (q * S + p) * H + k < B * S * H := by
      rw [hrEq]
      calc
        row * H + k < row * H + H := Nat.add_lt_add_left hk _
        _ = (row + 1) * H := by ring
        _ ≤ (B * S) * H := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hrow)
    rw [source_layernorm_chunk0_flat D u B S H fullx hfullx hD hu hS hH _ hbnd]
    congr 1
    ring
  have hm : layerNormMeanAt (chunkPrimDimN 0 D u fullx) (q * S + p) H =
      layerNormMeanAt fullx ((u * B + q) * S + p) H := by
    unfold layerNormMeanAt
    congr 1
    exact Finset.sum_congr rfl (fun k hk => hread k (Finset.mem_range.mp hk))
  have hv : ∀ mean,
      layerNormVarAt (chunkPrimDimN 0 D u fullx) (q * S + p) H mean =
        layerNormVarAt fullx ((u * B + q) * S + p) H mean := by
    intro mean
    unfold layerNormVarAt
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hread k (Finset.mem_range.mp hk)]
  rw [source_layernorm_chunk0_flat D u B S H
    (fw_layernorm fullx gamma beta) hglobal hD hu hS hH idx hi]
  have hglobalIdx : u * (B * S * H) + idx =
      (((u * B + q) * S + p) * H + j) := by
    calc
      _ = u * (B * S * H) + ((q * S + p) * H + j) := by rw [hiEq]
      _ = _ := by ring
  rw [hglobalIdx, ← hiEq]
  rw [fw_layernorm_valAt_3d fullx gamma beta (B * D) S H (u * B + q) p j
    hS hH hqfull hp hj hfullx]
  rw [fw_layernorm_valAt_3d (chunkPrimDimN 0 D u fullx) gamma beta B S H q p j
    hS hH hq hp hj hlocal]
  dsimp only
  rw [hm, hv, hread j hj]

/-- Within one DP unit, ordered TP sequence shards reconstruct LayerNorm.
The predecessor value equality is an input fact, never an output assumption. -/
theorem source_layernorm_unit_reconstruct
    (D T B S H u : Nat) (fullx gamma beta : Tensor) (xs : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S * T, H])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, H])
    (hgamma : gamma.shape = [H]) (hbeta : beta.shape = [H])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 1 T 0 xs) :
    chunkPrimDimN 0 D u (fw_layernorm fullx gamma beta) =
      allGatherPrimDimN 1 T 0 (xs.map (fun x => fw_layernorm x gamma beta)) := by
  rw [fw_layernorm_batch_chunk_dim0 D u B (S * T) H fullx gamma beta
    hD hB (Nat.mul_pos hS hT) hH hu hfullx hgamma hbeta, hpre]
  exact fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d
    T B S H xs gamma beta hT hB hS hH hlen hshapes hgamma hbeta

/-- Source-output adapter: individual producer equations yield the global
shape, every local shape, and the reconstructed value. `Forall₂` expresses
ordered local execution and does not assume the desired reconstruction. -/
theorem source_layernorm_unit_output_reconstruct
    (D T B S H u : Nat) (fullx gamma beta globalOut : Tensor)
    (xs localOuts : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S * T, H])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, H])
    (hgamma : gamma.shape = [H]) (hbeta : beta.shape = [H])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 1 T 0 xs)
    (hglobal : globalOut = fw_layernorm fullx gamma beta)
    (hlocal : List.Forall₂ (fun x y => y = fw_layernorm x gamma beta) xs localOuts) :
    globalOut.shape = [B * D, S * T, H] ∧
      (∀ y ∈ localOuts, y.shape = [B, S, H]) ∧
      chunkPrimDimN 0 D u globalOut = allGatherPrimDimN 1 T 0 localOuts := by
  have transport : ∀ {ins outs : List Tensor},
      List.Forall₂ (fun x y => y = fw_layernorm x gamma beta) ins outs →
      outs = ins.map (fun x => fw_layernorm x gamma beta) := by
    intro ins outs heq
    induction heq with
    | nil => rfl
    | cons hxy hrest ih => exact congrArg₂ List.cons hxy ih
  have houts : localOuts = xs.map (fun x => fw_layernorm x gamma beta) := transport hlocal
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal, source_layernorm_shape]
    exact hfullx
  · intro y hy
    rw [houts] at hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact (source_layernorm_shape x gamma beta).trans (hshapes x hx)
  · rw [hglobal, houts]
    exact source_layernorm_unit_reconstruct D T B S H u fullx gamma beta xs
      hD hT hB hS hH hu hfullx hlen hshapes hgamma hbeta hpre

#print axioms fw_layernorm_batch_chunk_dim0
#print axioms source_layernorm_unit_reconstruct
#print axioms source_layernorm_unit_output_reconstruct

end
end TrainVerify.Denote
