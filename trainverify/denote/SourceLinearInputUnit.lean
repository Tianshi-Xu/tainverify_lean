import denote.SourceLinearUnit
import denote.KRankLinearReduction

/-!
# Input-sharded source linear within one DP unit

Ordered input-feature and weight-column shards yield full and local output
shapes and a sum reduction of the local linear producers. This mathematical
adapter does not assert any concrete forward-stage or public completion.
-/

namespace TrainVerify.Denote
noncomputable section

/-- Input-feature-sharded source inputs and matching weight-column shards
reduce to the batch chunk of the global linear output. Output shapes are
conclusions, not assumptions; local producers retain their ordered pairing. -/
theorem source_linear_input_unit_output_reduce
    (D T B S I O u : Nat) (fullx fullweight globalOut : Tensor)
    (xs ws localOuts : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B)
    (hS : 0 < S) (hI : 0 < I) (hO : 0 < O)
    (hu : u < D) (hfullx : fullx.shape = [B * D, S, I * T])
    (hxlen : xs.length = T) (hwlen : ws.length = T)
    (hxshapes : ∀ x ∈ xs, x.shape = [B, S, I])
    (hwshapes : ∀ w ∈ ws, w.shape = [O, I])
    (hpre : chunkPrimDimN 0 D u fullx = allGatherPrimDimN 2 T 0 xs)
    (hweight : fullweight = allGatherPrimDimN 1 T 0 ws)
    (hglobal : globalOut = fw_linear fullx fullweight)
    (hlocal : List.Forall₂ (fun xy y => y = fw_linear xy.1 xy.2) (xs.zip ws) localOuts) :
    globalOut.shape = [B * D, S, O] ∧
      (∀ y ∈ localOuts, y.shape = [B, S, O]) ∧
      chunkPrimDimN 0 D u globalOut = tensorSum localOuts := by
  have hwhead : (ws.head?.map (fun t => t.shape)).getD [] = [O, I] := by
    cases heq : ws with
    | nil => simp only [heq, List.length_nil] at hwlen; omega
    | cons w rest =>
      simp only [List.head?, Option.map, Option.getD]
      exact hwshapes w (heq ▸ List.mem_cons_self ..)
  have hwfull : fullweight.shape = [O, I * T] := by
    rw [hweight, allGatherPrimDimN_shape 1 T ws [O, I] hwhead]
    rfl
  have hxunit : (chunkPrimDimN 0 D u fullx).shape = [B, S, I * T] := by
    rw [chunkPrimDimN_shape 0 D u fullx _ hfullx hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have transport : ∀ {ins : List (Tensor × Tensor)} {outs : List Tensor},
      List.Forall₂ (fun xy y => y = fw_linear xy.1 xy.2) ins outs →
      outs = ins.map (fun xy => fw_linear xy.1 xy.2) := by
    intro ins outs heq
    induction heq with
    | nil => rfl
    | cons hxy hrest ih => exact congrArg₂ List.cons hxy ih
  have houts := transport hlocal
  have hpieces : (List.ofFn (fun r : Fin T =>
      fw_linear (chunkPrim T r.val (chunkPrimDimN 0 D u fullx))
        (ws.get ⟨r.val, by omega⟩))) = localOuts := by
    rw [houts]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, List.length_zip, hxlen, hwlen, Nat.min_self]
    · intro r hr hl
      have hrT : r < T := by simpa only [List.length_ofFn] using hr
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_zip,
        List.get_eq_getElem]
      have hchunk : chunkPrim T r (chunkPrimDimN 0 D u fullx) =
          xs.get ⟨r, by omega⟩ := by
        rw [hpre]
        exact chunkPrim_allGatherPrimDimN_cancel_3d T r B S I xs hxlen hxshapes
          hT hB hS hI hrT
      exact congrArg (fun x => fw_linear x (ws.get ⟨r, by omega⟩)) hchunk
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact fw_linear_3d_shape (B * D) S (I * T) O fullx fullweight hfullx hwfull
  · intro y hy
    rw [houts] at hy
    obtain ⟨⟨x, w⟩, hmem, rfl⟩ := List.mem_map.mp hy
    exact fw_linear_3d_shape B S I O x w
      (hxshapes x (List.of_mem_zip hmem).1) (hwshapes w (List.of_mem_zip hmem).2)
  · rw [hglobal, fw_linear_batch_chunk_dim0 D u B S (I * T) O fullx fullweight
      hD hB hS (Nat.mul_pos hI hT) hO hu hfullx hwfull, hweight,
      allGatherPrimDimN_1_eq_allGatherPrim_2d T ws O I hwhead hI hT,
      fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d T B S (I * T) O I
        (chunkPrimDimN 0 D u fullx) ws hxunit (Nat.mul_comm I T)
        hwlen hwshapes hT hI hS hO, hpieces]
    cases localOuts <;> rfl

#print axioms source_linear_input_unit_output_reduce

end
end TrainVerify.Denote
