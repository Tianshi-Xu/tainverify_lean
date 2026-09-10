import denote.KRankViewUnflatten

/-!
# Source rank-3 to rank-4 views within one DP unit

A contiguous batch chunk commutes with the faithful flat-value `fw_view`.
The two source-output adapters preserve the complete ordered TP shard list,
using the existing sequence/head unflatten gather theorems. Their only output
hypotheses are individual actual producer equations.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

-- The existing equal-product view read helpers are private to their modules.
private theorem source_view_valAt_of_prod
    (target : Shape) (x : Tensor) (idx : Nat)
    (hprod : prodShape target = prodShape x.shape) :
    valAt (fw_view target x) idx = valAt x idx := by
  unfold fw_view valAt
  simp only [Tensor.mkShape]
  split <;> split <;> simp_all

-- Bounded contiguous read, independent of the number of trailing dimensions.
-- This only exposes the existing chunk semantics; it changes no operator.
private theorem source_view_chunk0_flat
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

/-- A legal batch-DP chunk commutes with rank-3 to rank-4 unflatten.
The selected DP rank is bounded; all trailing dimensions remain intact. -/
theorem fw_view_unflatten_batch_chunk_dim0
    (D u B S H C : Nat) (fullx : Tensor)
    (hD : 0 < D) (_hB : 0 < B) (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, H * C]) :
    chunkPrimDimN 0 D u (fw_view [B * D, S, H, C] fullx) =
      fw_view [B, S, H, C] (chunkPrimDimN 0 D u fullx) := by
  have hglobal : (fw_view [B * D, S, H, C] fullx).shape =
      [B * D, S, H, C] := rfl
  have hlocal : (chunkPrimDimN 0 D u fullx).shape = [B, S, H * C] := by
    rw [chunkPrimDimN_shape 0 D u fullx _ hfullx hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hleft : (chunkPrimDimN 0 D u
      (fw_view [B * D, S, H, C] fullx)).shape = [B, S, H, C] := by
    rw [chunkPrimDimN_shape 0 D u _ _ hglobal hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hfullProd : prodShape [B * D, S, H, C] = prodShape fullx.shape := by
    rw [hfullx]
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
  have hlocalProd : prodShape [B, S, H, C] =
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
  have hviewRead := source_view_chunk0_flat D u B (S * (H * C))
    (fw_view [B * D, S, H, C] fullx) hD hu hstride
    (by rw [hglobal]; rfl)
    (by simp only [hglobal, List.drop, List.foldl, Nat.one_mul, Nat.mul_assoc])
    idx hi hidx
  have hinputRead := source_view_chunk0_flat D u B (S * (H * C)) fullx
    hD hu hstride (by rw [hfullx]; rfl)
    (by simp only [hfullx, List.drop, List.foldl, Nat.one_mul, Nat.mul_assoc])
    idx hi hinputBound
  rw [hviewRead, source_view_valAt_of_prod _ _ _ hfullProd,
    source_view_valAt_of_prod _ _ _ hlocalProd, hinputRead]

-- Keep unrelated shape/length hypotheses out of the induction motive.
private theorem source_view_outputs_eq_map
    (target : Shape) {xs ys : List Tensor}
    (hlocal : List.Forall₂ (fun x y => y = fw_view target x) xs ys) :
    ys = xs.map (fun x => fw_view target x) := by
  induction hlocal with
  | nil => rfl
  | cons hxy hrest ih => exact congrArg₂ List.cons hxy ih

/-- Sequence-sharded rank-3 source values yield both output shapes and the
ordered rank-4 sequence reconstruction within the selected DP unit. -/
theorem source_view_sequence_unit_output_reconstruct
    (D T B S H C u : Nat) (fullx globaly : Tensor) (xs ys : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S * T, H * C])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, H * C])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 1 T 0 xs)
    (hglobal : globaly = fw_view [B * D, S * T, H, C] fullx)
    (hlocal : List.Forall₂ (fun x y => y = fw_view [B, S, H, C] x) xs ys) :
    globaly.shape = [B * D, S * T, H, C] ∧
      (∀ y ∈ ys, y.shape = [B, S, H, C]) ∧
      chunkPrimDimN 0 D u globaly = allGatherPrimDimN 1 T 0 ys := by
  have houts := source_view_outputs_eq_map [B, S, H, C] hlocal
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg Tensor.shape hglobal
  · intro y hy
    rw [houts] at hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    rfl
  · rw [hglobal, houts,
      fw_view_unflatten_batch_chunk_dim0 D u B (S * T) H C fullx
        hD hB (Nat.mul_pos hS hT) hH hC hu hfullx, hpre]
    exact TrainVerify.Denote.fw_view_unflatten_allGather_dim1_rank3
      T B S H C xs hT hB hS hH hC hlen hshapes

/-- Head-sharded rank-3 source values yield both output shapes and the ordered
rank-4 head reconstruction. TP head arithmetic is delegated to the existing
unflatten gather theorem, rather than assumed as an output equality. -/
theorem source_view_head_unit_output_reconstruct
    (D T B S H C u : Nat) (fullx globaly : Tensor) (xs ys : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hH : 0 < H) (hC : 0 < C)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, (H * T) * C])
    (hlen : xs.length = T) (hshapes : ∀ x ∈ xs, x.shape = [B, S, H * C])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 2 T 0 xs)
    (hglobal : globaly = fw_view [B * D, S, H * T, C] fullx)
    (hlocal : List.Forall₂ (fun x y => y = fw_view [B, S, H, C] x) xs ys) :
    globaly.shape = [B * D, S, H * T, C] ∧
      (∀ y ∈ ys, y.shape = [B, S, H, C]) ∧
      chunkPrimDimN 0 D u globaly = allGatherPrimDimN 2 T 0 ys := by
  have houts := source_view_outputs_eq_map [B, S, H, C] hlocal
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg Tensor.shape hglobal
  · intro y hy
    rw [houts] at hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    rfl
  · rw [hglobal, houts,
      fw_view_unflatten_batch_chunk_dim0 D u B S (H * T) C fullx
        hD hB hS (Nat.mul_pos hH hT) hC hu hfullx, hpre]
    exact TrainVerify.Denote.fw_view_unflatten_allGather_dim2_rank3
      T B S H C xs hT hB hS hH hC hlen hshapes

#print axioms fw_view_unflatten_batch_chunk_dim0
#print axioms source_view_sequence_unit_output_reconstruct
#print axioms source_view_head_unit_output_reconstruct

end
end TrainVerify.Denote
