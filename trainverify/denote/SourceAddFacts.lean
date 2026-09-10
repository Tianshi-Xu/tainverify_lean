import denote.SourceAddUnit

namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

private theorem source_add_zip_shapes (sh : Shape) (As Bs : List Tensor)
    (hA : ∀ x ∈ As, x.shape = sh) (hB : ∀ x ∈ Bs, x.shape = sh) :
    ∀ x ∈ List.zipWith elemwiseAdd As Bs, x.shape = sh := by
  induction As generalizing Bs with
  | nil => simp only [List.zipWith_nil_left, List.not_mem_nil, false_implies, implies_true]
  | cons a rest ih =>
    cases Bs with
    | nil => simp only [List.zipWith_nil_right, List.not_mem_nil, false_implies, implies_true]
    | cons b bs =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact elemwiseAdd_shape_of_shapes a b sh (hA a List.mem_cons_self) (hB b List.mem_cons_self)
      · exact ih bs (fun y hy => hA y (List.mem_cons_of_mem a hy))
          (fun y hy => hB y (List.mem_cons_of_mem b hy)) x hx

/-- Reusable source-add facts retain the global shape, every local output shape,
and the original per-unit value reconstruction. No output shape is assumed. -/
theorem source_add_unit_output_facts
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
    globalOut.shape = [B * D, S, H * T] ∧
    (∀ x ∈ localOuts, x.shape = [B, S, H]) ∧
    chunkPrimDimN 0 D u globalOut = allGatherPrimDimN 2 T 0 localOuts := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact elemwiseAdd_shape_of_shapes fullA fullB _ hfullA hfullB
  · rw [hlocal]
    apply source_add_zip_shapes
    · intro x hx
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
      rw [← hi]
      exact hAshapes i.val i.isLt
    · intro x hx
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
      rw [← hi]
      exact hBshapes i.val i.isLt
  · exact source_add_unit_output_reconstruct D T B S H u fullA fullB globalOut As Bs localOuts
      hD hT hBpos hS hH hu hfullA hfullB hAs hBs hAshapes hBshapes hA hB hglobal hlocal

#print axioms source_add_unit_output_facts
end
end TrainVerify.Denote
