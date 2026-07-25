/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagLayoutRel

/-!
# Row-local `fw_mix_precision_linear` preserves the CP2 zigzag layout relation

The generated graph contains `FW_mix_precision_linear` nodes whose weight is
*replicated* across the two context-parallel ranks (single-machine node 507 with
shapes `[4096, 1024] → [4096, 1024]`, per-rank nodes 1072/1073 with
`[2048, 1024] → [2048, 1024]`).  `evalOp` dispatches `FW_mix_precision_linear`
to `fw_linear x w` (see `evalOp_fw_mix_precision_linear_iroha`), which for a 2-D
input `[lDim, inDim]` and a 2-D weight `[outDim, inDim]` is the ordinary
row-local matrix product: output row `i` depends only on input row `i`.

Consequently the operation commutes with both CP2 collectives:

* the dim-0 all-gather — already available in the core library as
  `fw_mix_precision_linear_allGather0_commute_2`;
* the faithful CP2 shuffle `fw_maybe_shuffle_collective`, which only permutes
  *whole rows* (its index arithmetic uses `chunk = shape.getD 0 0 = lDim` and
  `hiddenStride = prodShape shape.tail`, the latter changing from `inDim` to
  `outDim` but staying a full-row stride on both sides).

Nothing here claims anything about weights that are themselves sharded.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-! ## Elementary 2-D `fw_linear` facts -/

/-- Shape of the 2-D row-local linear. -/
theorem fw_linear_shape_2d' (lDim inDim outDim : Nat) (x w : Tensor)
    (hx : x.shape = [lDim, inDim]) (hw : w.shape = [outDim, inDim]) :
    (fw_linear x w).shape = [lDim, outDim] := by
  rw [fw_linear_is_matmul lDim inDim outDim x w hx hw]; rfl

/-- Row-local value equation for the 2-D linear: output entry `(row, c)` is the
dot product of input row `row` with weight row `c`. -/
theorem fw_linear_valAt_2d' (lDim inDim outDim : Nat) (x w : Tensor)
    (hout : 0 < outDim)
    (hx : x.shape = [lDim, inDim]) (hw : w.shape = [outDim, inDim])
    (row c : Nat) (hrow : row < lDim) (hc : c < outDim) :
    valAt (fw_linear x w) (row * outDim + c) =
      ∑ j ∈ Finset.range inDim,
        valAt x (row * inDim + j) * valAt w (c * inDim + j) := by
  have hbound : row * outDim + c < prodShape [lDim, outDim] := by
    simp only [prodShape, List.foldl, Nat.one_mul]
    calc row * outDim + c < row * outDim + outDim := Nat.add_lt_add_left hc _
      _ = (row + 1) * outDim := by ring
      _ ≤ lDim * outDim := Nat.mul_le_mul_right _ hrow
  rw [fw_linear_is_matmul lDim inDim outDim x w hx hw]
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hbound)]
  have hdiv : (row * outDim + c) / outDim = row := by
    rw [show row * outDim + c = c + outDim * row by ring,
      Nat.add_mul_div_left _ _ hout, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (row * outDim + c) % outDim = c := by
    rw [show row * outDim + c = c + outDim * row by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  show (∑ j ∈ Finset.range inDim,
      valAt x ((row * outDim + c) / outDim * inDim + j) *
        valAt w ((row * outDim + c) % outDim * inDim + j)) = _
  rw [hdiv, hmod]

/-! ## `fw_linear` commutes with the faithful CP2 shuffle -/

/-- A faithful CP2 shuffle commutes with the row-local 2-D linear: the shuffle
moves complete rows, and every output row reads exactly one input row. -/
theorem fw_mix_precision_linear_shuffle_collective_cp2
    (source0 source1 w : Tensor) (cu : List Nat)
    (lDim inDim outDim rank : Nat)
    (hl : 0 < lDim) (hin : 0 < inDim) (hout : 0 < outDim) (hrank : rank < 2)
    (hs0 : source0.shape = [lDim, inDim])
    (hs1 : source1.shape = [lDim, inDim])
    (hw : w.shape = [outDim, inDim]) :
    fw_linear (fw_maybe_shuffle_collective [source0, source1] cu 2 rank) w =
      fw_maybe_shuffle_collective
        [fw_linear source0 w, fw_linear source1 w] cu 2 rank := by
  have hr : rank = 0 ∨ rank = 1 := by omega
  have hlocal : ([source0, source1].getD rank (zeroTensor [])).shape =
      [lDim, inDim] := by
    rcases hr with rfl | rfl
    · simpa only [List.getD_cons_zero] using hs0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
  have hL0 := fw_linear_shape_2d' lDim inDim outDim source0 w hs0 hw
  have hL1 := fw_linear_shape_2d' lDim inDim outDim source1 w hs1 hw
  have hlocalL : ([fw_linear source0 w, fw_linear source1 w].getD rank
      (zeroTensor [])).shape = [lDim, outDim] := by
    rcases hr with rfl | rfl
    · simpa only [List.getD_cons_zero] using hL0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hL1
  have hshuffleShape :
      (fw_maybe_shuffle_collective [source0, source1] cu 2 rank).shape =
        [lDim, inDim] := by
    rw [fw_maybe_shuffle_collective_shape]; exact hlocal
  have hleftShape := fw_linear_shape_2d' lDim inDim outDim
    (fw_maybe_shuffle_collective [source0, source1] cu 2 rank) w
    hshuffleShape hw
  apply Tensor.ext
  · rw [hleftShape, fw_maybe_shuffle_collective_shape, hlocalL]
  · intro idx hidx
    rw [hleftShape] at hidx
    have hib : idx < lDim * outDim := by
      simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
    set row := idx / outDim with hrowdef
    set c := idx % outDim with hcdef
    have hc : c < outDim := Nat.mod_lt _ hout
    have hrow : row < lDim := (Nat.div_lt_iff_lt_mul hout).mpr hib
    have hidxEq : idx = row * outDim + c := by
      rw [hrowdef, hcdef]; exact (Nat.div_add_mod' idx outDim).symm
    set global := zigzagPos cu 2 rank row with hgdef
    have hsrcRow : global % lDim < lDim := Nat.mod_lt _ hl
    -- reading one shuffled input row is reading a source row
    have hinput (j : Nat) (hj : j < inDim) :
        valAt (fw_maybe_shuffle_collective [source0, source1] cu 2 rank)
            (row * inDim + j) =
          valAt ([source0, source1].getD (global / lDim) (zeroTensor []))
            (global % lDim * inDim + j) := by
      rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)]
      · simp only [hlocal, List.tail_cons, prodShape, List.foldl,
          Nat.one_mul, List.getD_cons_zero]
        rw [show row * inDim + j = j + inDim * row by ring,
          Nat.add_mul_div_left _ _ hin, Nat.div_eq_of_lt hj, Nat.zero_add,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
        rfl
      · rw [hlocal]
        simp only [prodShape, List.foldl, Nat.one_mul]
        calc row * inDim + j < row * inDim + inDim := Nat.add_lt_add_left hj _
          _ = (row + 1) * inDim := by ring
          _ ≤ lDim * inDim := Nat.mul_le_mul_right _ hrow
    rw [hidxEq]
    rw [fw_linear_valAt_2d' lDim inDim outDim _ w hout hshuffleShape hw
      row c hrow hc]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocalL]
          simp only [prodShape, List.foldl, Nat.one_mul]
          calc row * outDim + c < row * outDim + outDim :=
              Nat.add_lt_add_left hc _
            _ = (row + 1) * outDim := by ring
            _ ≤ lDim * outDim := Nat.mul_le_mul_right _ hrow)]
    simp only [hlocalL, List.tail_cons, prodShape, List.foldl,
      Nat.one_mul, List.getD_cons_zero]
    rw [show row * outDim + c = c + outDim * row by ring,
      Nat.add_mul_div_left _ _ hout, Nat.div_eq_of_lt hc, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    unfold gatherFromRank
    rw [← hgdef]
    -- the source row index shared by both sides
    have hib' : global % lDim * outDim + c < lDim * outDim := by
      calc global % lDim * outDim + c < global % lDim * outDim + outDim :=
          Nat.add_lt_add_left hc _
        _ = (global % lDim + 1) * outDim := by ring
        _ ≤ lDim * outDim := Nat.mul_le_mul_right _ hsrcRow
    by_cases h0 : global / lDim = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      rw [fw_linear_valAt_2d' lDim inDim outDim source0 w hout hs0 hw
        (global % lDim) c hsrcRow hc]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hinput j (Finset.mem_range.mp hj), h0]
      simp only [List.getD_cons_zero]
    · by_cases h1 : global / lDim = 1
      · rw [h1]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        rw [fw_linear_valAt_2d' lDim inDim outDim source1 w hout hs1 hw
          (global % lDim) c hsrcRow hc]
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [hinput j (Finset.mem_range.mp hj), h1]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
      · have hge : ∀ n : Nat, ¬ n = 0 → ¬ n = 1 → 2 ≤ n := by intro n a b; omega
        have hnot : 2 ≤ global / lDim := hge _ h0 h1
        have hgetA : [source0, source1].getD (global / lDim) (zeroTensor []) =
            zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        have hgetB : [fw_linear source0 w, fw_linear source1 w].getD
            (global / lDim) (zeroTensor []) = zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        show (∑ j ∈ Finset.range inDim,
            valAt (fw_maybe_shuffle_collective [source0, source1] cu 2 rank)
              (row * inDim + j) * valAt w (c * inDim + j)) =
          valAt ([fw_linear source0 w, fw_linear source1 w].getD
            (global / lDim) (zeroTensor [])) (global % lDim * outDim + c)
        rw [hgetB]
        rw [valAt_zeroTensor_empty]
        refine Finset.sum_eq_zero ?_
        intro j hj
        rw [hinput j (Finset.mem_range.mp hj), hgetA,
          valAt_zeroTensor_empty, zero_mul]

/-! ## Metadata well-formedness transports along the linear -/

/-- Applying the row-local linear to both CP2 source shards preserves
packed-sequence well-formedness: the contract only mentions metadata and the
dim-0 token count, which the linear leaves untouched (only the trailing axis
changes from `inDim` to `outDim`). -/
theorem ZigzagCuWF.mix_precision_linear_cp2
    (cu : List Nat) (source0 source1 w : Tensor) (lDim inDim outDim : Nat)
    (hwf : ZigzagCuWF cu [source0, source1] 2)
    (hs0 : source0.shape = [lDim, inDim])
    (hs1 : source1.shape = [lDim, inDim])
    (hw : w.shape = [outDim, inDim]) :
    ZigzagCuWF cu [fw_linear source0 w, fw_linear source1 w] 2 := by
  have hL0 := fw_linear_shape_2d' lDim inDim outDim source0 w hs0 hw
  have hL1 := fw_linear_shape_2d' lDim inDim outDim source1 w hs1 hw
  refine ⟨hwf.cp_pos, rfl, hwf.cu_starts_zero, hwf.cu_has_endpoint,
    hwf.monotone, hwf.divisible, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hL0]; exact List.cons_ne_nil _ _
    · rw [hL1]; exact List.cons_ne_nil _ _
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rfl
    · simp only [List.getD_cons_zero]
      rw [hL1, hL0]
  · have h := hwf.local_tokens
    simp only [List.getD_cons_zero, hs0] at h
    simpa only [List.getD_cons_zero, hL0] using h

namespace Zigzag2Rel

/-- A replicated 2-D weight preserves the source-witness zigzag relation.  This
models the graph's `FW_mix_precision_linear` node (`evalOp` dispatches it to
`fw_linear`): the operation is row-local, hence commutes both with the ordinary
dim-0 all-gather and with each faithful CP2 shuffled rank. -/
theorem mix_precision_linear
    {full z0 z1 cu w : Tensor} (lDim inDim outDim : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, inDim] [lDim, inDim])
    (hw : w.shape = [outDim, inDim])
    (hl : 0 < lDim) (hin : 0 < inDim) (hout : 0 < outDim) :
    Zigzag2Rel
      (fw_linear full w) (fw_linear z0 w) (fw_linear z1 w)
      cu [lDim * 2, outDim] [lDim, outDim] := by
  rcases hrel with ⟨source0, source1, hs⟩
  have hs0 : source0.shape = [lDim, inDim] := hs.source0_shape
  have hs1 : source1.shape = [lDim, inDim] := hs.source1_shape
  have hfullActual : full.shape = [lDim * 2, inDim] := hs.full_shape
  have hL0 := fw_linear_shape_2d' lDim inDim outDim source0 w hs0 hw
  have hL1 := fw_linear_shape_2d' lDim inDim outDim source1 w hs1 hw
  refine ⟨fw_linear source0 w, fw_linear source1 w,
    ?_, ?_, ?_, ?_, hL0, hL1, ?_, ?_,
    ZigzagCuWF.mix_precision_linear_cp2 _ source0 source1 w lDim inDim outDim
      hs.cu_wf hs0 hs1 hw⟩
  · rw [hs.full_value]
    exact fw_mix_precision_linear_allGather0_commute_2
      source0 source1 w lDim inDim outDim hl hin hout hs0 hs1 hw
  · rw [hs.rank0_value]
    exact fw_mix_precision_linear_shuffle_collective_cp2
      source0 source1 w (decodeCuSeqlens cu) lDim inDim outDim 0
      hl hin hout (by decide) hs0 hs1 hw
  · rw [hs.rank1_value]
    exact fw_mix_precision_linear_shuffle_collective_cp2
      source0 source1 w (decodeCuSeqlens cu) lDim inDim outDim 1
      hl hin hout (by decide) hs0 hs1 hw
  · exact fw_linear_shape_2d' (lDim * 2) inDim outDim full w hfullActual hw
  · exact fw_linear_shape_2d' lDim inDim outDim z0 w hs.rank0_shape hw
  · exact fw_linear_shape_2d' lDim inDim outDim z1 w hs.rank1_shape hw

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
