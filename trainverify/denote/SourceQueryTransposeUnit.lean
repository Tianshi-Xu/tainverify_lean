import denote.SourceTransposeUnit

/-!
# Source query transpose12 within one DP unit

Query shards on input axis 2 move to output axis 1. The ordered TP output
list is derived from the actual individual transpose equations; no output
shape or output reconstruction is assumed. This is a Denote tensor theorem
(over its real-valued scalar model), not a floating-point Torch claim.

The proof reuses the existing batch-chunk and dim2-to-dim1 gather theorems.
The heartbeat bound below applies only to the new declarations, not to the
historical proof of the imported gather theorem.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

private theorem source_query_transpose12_shape
    (x : Tensor) (B S H C : Nat) (hx : x.shape = [B, S, H, C]) :
    (transposeAxes 1 2 x).shape = [B, H, S, C] := by
  change listSwapAt x.shape 1 2 = [B, H, S, C]
  rw [hx]
  rfl

private theorem source_query_transpose12_outputs_eq_map {xs ys : List Tensor}
    (hlocal : List.Forall₂ (fun x y => y = transposeAxes 1 2 x) xs ys) :
    ys = xs.map (transposeAxes 1 2) := by
  induction hlocal with
  | nil => rfl
  | cons hxy hrest ih => exact congrArg₂ List.cons hxy ih

/-- Query shards move from axis 2 to axis 1 within the selected batch-DP unit. -/
theorem source_transpose12_query_unit_output_reconstruct
    (D T B S H C u : Nat) (fullx globaly : Tensor) (xs ys : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H * T, C])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, H, C])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 2 T 0 xs)
    (hglobal : globaly = transposeAxes 1 2 fullx)
    (hlocal : List.Forall₂ (fun x y => y = transposeAxes 1 2 x) xs ys) :
    globaly.shape = [B * D, H * T, S, C] ∧
      (∀ y ∈ ys, y.shape = [B, H, S, C]) ∧
      chunkPrimDimN 0 D u globaly = allGatherPrimDimN 1 T 0 ys := by
  have houts := source_query_transpose12_outputs_eq_map hlocal
  have hne : xs ≠ [] := by
    intro hempty
    have hz : xs.length = 0 := by rw [hempty]; rfl
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact source_query_transpose12_shape fullx (B * D) S (H * T) C hfullx
  · intro y hy
    rw [houts] at hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact source_query_transpose12_shape x B S H C (hshapes x hx)
  · rw [hglobal, houts,
      transposeAxes_1_2_batch_chunk_dim0 D u B S (H * T) C fullx
        hD hB hS (Nat.mul_pos hH hT) hC hu hfullx, hpre]
    have htp := transposeAxes_1_2_allGather_dim2_to_dim1_rank4
      xs B S H C hne hshapes
    rw [hlen] at htp
    exact htp

#print axioms source_transpose12_query_unit_output_reconstruct

end
end TrainVerify.Denote
