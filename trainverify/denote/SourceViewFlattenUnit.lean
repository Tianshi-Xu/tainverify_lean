import denote.KRankViewFlatten

/-!
# Source rank-4 to rank-3 flattening within one batch unit

Contiguous batch chunks commute with the flat-value `fw_view` denotation.
The head-sharded adapter derives global and local output shapes and ordered
head reconstruction from input geometry and actual producer equations.
This is a mathematical Denote library result, not a DP ownership, source
capture, raw view-kwargs, or runtime Torch fidelity claim.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

-- Equal-product view reads and contiguous chunk reads are private in the
-- existing modules. Expose only their small local proof patterns here.
private theorem source_view_flatten_valAt_of_prod
    (target : Shape) (x : Tensor) (idx : Nat)
    (hprod : prodShape target = prodShape x.shape) :
    valAt (fw_view target x) idx = valAt x idx := by
  unfold fw_view valAt
  simp only [Tensor.mkShape]
  split <;> split <;> simp_all

private theorem source_view_flatten_chunk0_flat
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

/-- Flattening the trailing two axes commutes with a legal contiguous batch
chunk. All dimensions are positive and the selected batch rank is bounded. -/
theorem fw_view_flatten_batch_chunk_dim0
    (D B S H C u : Nat) (fullx : Tensor)
    (hD : 0 < D) (hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H, C]) :
    fw_view [B, S, H * C] (chunkPrimDimN 0 D u fullx) =
      chunkPrimDimN 0 D u (fw_view [B * D, S, H * C] fullx) := by
  symm
  have hglobal : (fw_view [B * D, S, H * C] fullx).shape =
      [B * D, S, H * C] := rfl
  have hlocal : (chunkPrimDimN 0 D u fullx).shape = [B, S, H, C] := by
    rw [chunkPrimDimN_shape 0 D u fullx _ hfullx hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hleft : (chunkPrimDimN 0 D u
      (fw_view [B * D, S, H * C] fullx)).shape = [B, S, H * C] := by
    rw [chunkPrimDimN_shape 0 D u _ _ hglobal hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hfullProd : prodShape [B * D, S, H * C] = prodShape fullx.shape := by
    rw [hfullx]
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
  have hlocalProd : prodShape [B, S, H * C] =
      prodShape (chunkPrimDimN 0 D u fullx).shape := by
    rw [hlocal]
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
  have hstride : 0 < S * (H * C) := Nat.mul_pos hS (Nat.mul_pos hH hC)
  apply Tensor.ext (by exact hleft)
  intro idx hidx
  have hi : idx < B * (S * (H * C)) := by
    rw [hleft] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hidx
  have hinputBound : idx < prodShape (chunkPrimDimN 0 D u fullx).shape := by
    rw [hlocal]
    simpa only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc] using hi
  have hviewRead := source_view_flatten_chunk0_flat D u B (S * (H * C))
    (fw_view [B * D, S, H * C] fullx) hD hu hstride
    (by rw [hglobal]; rfl)
    (by simp only [hglobal, List.drop, List.foldl, Nat.one_mul, Nat.mul_assoc])
    idx hi hidx
  have hinputRead := source_view_flatten_chunk0_flat D u B (S * (H * C)) fullx
    hD hu hstride (by rw [hfullx]; rfl)
    (by simp only [hfullx, List.drop, List.foldl, Nat.one_mul, Nat.mul_assoc])
    idx hi hinputBound
  rw [hviewRead, source_view_flatten_valAt_of_prod _ _ _ hfullProd,
    source_view_flatten_valAt_of_prod _ _ _ hlocalProd, hinputRead]

-- Keep the induction motive independent of input shapes and list length.
private theorem source_view_flatten_outputs_eq_map
    (target : Shape) {xs ys : List Tensor}
    (hlocal : List.Forall₂ (fun x y => y = fw_view target x) xs ys) :
    ys = xs.map (fun x => fw_view target x) := by
  induction hlocal with
  | nil => rfl
  | cons hxy hrest ih => exact congrArg₂ List.cons hxy ih

/-- Head-sharded rank-four inputs yield the complete rank-three output
geometry and ordered head reconstruction within the selected batch unit.
No output shape or output reconstruction is assumed. The head-gather
arithmetic is delegated to the existing generic flatten theorem. -/
theorem source_view_flatten_head_unit_output_reconstruct
    (D T B S H C u : Nat) (fullx globaly : Tensor) (xs ys : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H * T, C])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, H, C])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 2 T 0 xs)
    (hglobal : globaly = fw_view [B * D, S, (H * T) * C] fullx)
    (hlocal : List.Forall₂ (fun x y => y = fw_view [B, S, H * C] x) xs ys) :
    globaly.shape = [B * D, S, (H * T) * C] ∧
      (∀ y ∈ ys, y.shape = [B, S, H * C]) ∧
      chunkPrimDimN 0 D u globaly = allGatherPrimDimN 2 T 0 ys := by
  have houts := source_view_flatten_outputs_eq_map [B, S, H * C] hlocal
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg Tensor.shape hglobal
  · intro y hy
    rw [houts] at hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    rfl
  · rw [hglobal, houts,
      ← fw_view_flatten_batch_chunk_dim0 D B S (H * T) C u fullx
        hD hB hS (Nat.mul_pos hH hT) hC hu hfullx, hpre]
    exact TrainVerify.Denote.fw_view_allGatherPrimDimN_dim2_rank4_to_rank3
      T B S H C xs hT hB hS hH hC hlen hshapes

#print axioms fw_view_flatten_batch_chunk_dim0
#print axioms source_view_flatten_head_unit_output_reconstruct

end
end TrainVerify.Denote
