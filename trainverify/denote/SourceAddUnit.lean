import denote.KRankAddGather

/-!
# Source pointwise addition within one DP unit

Compose predecessor value reconstructions with their common-shape contracts:
DP selects batch dimension 0, and each ordered TP list reconstructs hidden
 dimension 2. The conclusion is derived, not supplied as an output premise.

Static candidate: compilation and the axiom commands below belong to the
parent's serial validation lane.
-/

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

-- Extend the existing bounded read lemma through valAt's zero default.
-- This avoids proving anything new about chunk's flat-index arithmetic.
private theorem source_add_valAt_same_shape_total
    (x y : Tensor) (sh : Shape) (hx : x.shape = sh) (hy : y.shape = sh)
    (idx : Nat) :
    valAt (elemwiseAdd x y) idx = valAt x idx + valAt y idx := by
  by_cases hi : idx < prodShape sh
  · exact elemwiseAdd_valAt_of_same_shape x y sh idx hx hy hi
  · have hs := elemwiseAdd_shape_of_shapes x y sh hx hy
    have hxout : ¬ idx < prodShape x.shape := by rw [hx]; exact hi
    have hyout : ¬ idx < prodShape y.shape := by rw [hy]; exact hi
    have hsout : ¬ idx < prodShape (elemwiseAdd x y).shape := by
      rw [hs]
      exact hi
    simp only [valAt, dif_neg hxout, dif_neg hyout, dif_neg hsout, add_zero]

/-- Equal-shaped 3D addition commutes with a DP batch chunk. No coordinate
arithmetic is needed: the three chunks use the same source read index.
The stronger helper permits zero extents and any rank (chunk uses rank modulo D). -/
theorem fw_add_batch_chunk_dim0
    (D u B S W : Nat) (x y : Tensor)
    (hD : 0 < D) (hx : x.shape = [B * D, S, W])
    (hy : y.shape = [B * D, S, W]) :
    chunkPrimDimN 0 D u (elemwiseAdd x y) =
      elemwiseAdd (chunkPrimDimN 0 D u x) (chunkPrimDimN 0 D u y) := by
  have hs : (elemwiseAdd x y).shape = [B * D, S, W] :=
    elemwiseAdd_shape_of_shapes x y _ hx hy
  have hc : ∀ t : Tensor, t.shape = [B * D, S, W] →
      (chunkPrimDimN 0 D u t).shape = [B, S, W] := by
    intro t ht
    rw [chunkPrimDimN_shape 0 D u t _ ht hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have hcx := hc x hx
  have hcy := hc y hy
  have hcs := hc (elemwiseAdd x y) hs
  have hlocal :
      (elemwiseAdd (chunkPrimDimN 0 D u x) (chunkPrimDimN 0 D u y)).shape =
        [B, S, W] :=
    elemwiseAdd_shape_of_shapes _ _ _ hcx hcy
  apply Tensor.ext (by rw [hcs, hlocal])
  intro idx hidx
  have hi : idx < prodShape [B, S, W] := by rw [hcs] at hidx; exact hidx
  have hix : idx < prodShape (chunkPrimDimN 0 D u x).shape := by
    rw [hcx]
    exact hi
  have hiy : idx < prodShape (chunkPrimDimN 0 D u y).shape := by
    rw [hcy]
    exact hi
  rw [elemwiseAdd_valAt_of_same_shape _ _ _ idx hcx hcy hi]
  rw [valAt_of_lt _ _ hidx, valAt_of_lt _ _ hix, valAt_of_lt _ _ hiy]
  simp only [chunkPrimDimN, Tensor.mkShape, hs, hx, hy]
  exact source_add_valAt_same_shape_total x y [B * D, S, W] hx hy _

/-- Pointwise source addition reconstructs within a DP unit from the ordered
TP output pairs. Only predecessor values and input shapes are assumed.
Positivity and the legal DP rank expose the intended source-layout contract;
the underlying chunk/add law itself needs only D positive. -/
theorem source_add_unit_reconstruct
    (D T B S H u : Nat) (fullA fullB : Tensor) (As Bs : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (_hB : 0 < B) (_hS : 0 < S) (_hH : 0 < H)
    (_hu : u < D)
    (hfullA : fullA.shape = [B * D, S, H * T])
    (hfullB : fullB.shape = [B * D, S, H * T])
    (hAs : As.length = T) (hBs : Bs.length = T)
    (hAshapes : ∀ r (hr : r < As.length), (As.get ⟨r, hr⟩).shape = [B, S, H])
    (hBshapes : ∀ r (hr : r < Bs.length), (Bs.get ⟨r, hr⟩).shape = [B, S, H])
    (hA : chunkPrimDimN 0 D u fullA = allGatherPrimDimN 2 T 0 As)
    (hB : chunkPrimDimN 0 D u fullB = allGatherPrimDimN 2 T 0 Bs) :
    chunkPrimDimN 0 D u (elemwiseAdd fullA fullB) =
      allGatherPrimDimN 2 T 0 (List.zipWith elemwiseAdd As Bs) := by
  have hAsne : As ≠ [] := by
    intro he
    have hz : As.length = 0 := by rw [he]; rfl
    omega
  have hlen : As.length = Bs.length := hAs.trans hBs.symm
  have hzip : (List.zipWith elemwiseAdd As Bs).length = T := by
    rw [List.length_zipWith, hAs, hBs, Nat.min_self]
  have hg := fw_add_allGather_dim_K 2 [B, S, H] As Bs hAsne hlen
    (by change 2 < 3; decide) hAshapes hBshapes
  rw [hzip, hAs, hBs] at hg
  rw [fw_add_batch_chunk_dim0 D u B S (H * T) fullA fullB hD hfullA hfullB,
    hA, hB]
  exact hg

/-- Thin output-name adapter. The local list equality specifies ordinary
ordered local execution, not the desired global reconstruction. -/
theorem source_add_unit_output_reconstruct
    (D T B S H u : Nat) (fullA fullB globalOut : Tensor)
    (As Bs localOuts : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hBpos : 0 < B) (hS : 0 < S) (hH : 0 < H)
    (hu : u < D)
    (hfullA : fullA.shape = [B * D, S, H * T])
    (hfullB : fullB.shape = [B * D, S, H * T])
    (hAs : As.length = T) (hBs : Bs.length = T)
    (hAshapes : ∀ r (hr : r < As.length), (As.get ⟨r, hr⟩).shape = [B, S, H])
    (hBshapes : ∀ r (hr : r < Bs.length), (Bs.get ⟨r, hr⟩).shape = [B, S, H])
    (hA : chunkPrimDimN 0 D u fullA = allGatherPrimDimN 2 T 0 As)
    (hB : chunkPrimDimN 0 D u fullB = allGatherPrimDimN 2 T 0 Bs)
    (hglobal : globalOut = elemwiseAdd fullA fullB)
    (hlocal : localOuts = List.zipWith elemwiseAdd As Bs) :
    chunkPrimDimN 0 D u globalOut = allGatherPrimDimN 2 T 0 localOuts := by
  rw [hglobal, hlocal]
  exact source_add_unit_reconstruct D T B S H u fullA fullB As Bs
    hD hT hBpos hS hH hu hfullA hfullB hAs hBs hAshapes hBshapes hA hB

#print axioms fw_add_batch_chunk_dim0
#print axioms source_add_unit_reconstruct
#print axioms source_add_unit_output_reconstruct

end
end TrainVerify.Denote
