/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagLayoutRel

/-!
# Row-local `fw_view` preserves the CP2 zigzag layout relation

The generated graph applies `FW_reshape` (semantically `fw_view`) with a
*shape-parameterised* target: the single-machine node uses `[4096, 1024]` while
each of the two partitioned ranks uses `[2048, 1024]`.  The shard input shape is
`[lDim, h, d]` and the target is `[lDim, h * d]`, i.e. the **row (dim-0) count is
unchanged** and only the trailing axes are merged.

This is exactly the regime in which a reshape commutes with the CP collectives:

* `fw_maybe_shuffle_collective` only uses `chunk = shape.getD 0 0` and
  `hiddenStride = prodShape shape.tail`.  Under `[lDim, h, d] ↦ [lDim, h * d]`
  both are unchanged (`prodShape [h, d] = h * d`), so the index arithmetic is
  literally the same and the reshape commutes with the shuffle.
* the dim-0 all-gather with an unchanged trailing stride is plain flat
  concatenation, so the reshape commutes with it too (the global target being
  `[lDim * 2, h * d]`).

No claim is made about general shape-changing reshapes: those do **not** commute
with an all-gather, and nothing here relies on such a statement.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-! ## Elementary `fw_view` facts -/

/-- `fw_view` produces exactly the requested shape. -/
@[simp] theorem fw_view_shape' (targetShape : Shape) (x : Tensor) :
    (fw_view targetShape x).shape = targetShape := rfl

/-- In range, `fw_view` is the identity on flat data. -/
theorem fw_view_valAt (targetShape : Shape) (x : Tensor) (m : Nat)
    (hm : m < prodShape targetShape) :
    valAt (fw_view targetShape x) m = valAt x m := by
  unfold fw_view
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hm)]
  rfl

/-- Flat product of a merged 3D shard shape. -/
theorem prodShape_view_2d (lDim hW dW : Nat) :
    prodShape [lDim, hW * dW] = lDim * (hW * dW) := by
  simp only [prodShape, List.foldl, Nat.one_mul]

theorem prodShape_shard_3d (lDim hW dW : Nat) :
    prodShape [lDim, hW, dW] = lDim * (hW * dW) := by
  simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]

/-! ## `fw_view` commutes with the CP2 dim-0 all-gather -/

/-- Merging the trailing axes of both CP2 shards commutes with the ordinary
dim-0 all-gather, because the trailing stride `hW * dW` is unchanged and dim 0 is
untouched: the gather is a flat concatenation on both sides. -/
theorem fw_view_allGather0_commute_cp2
    (source0 source1 : Tensor) (lDim hW dW : Nat)
    (hl : 0 < lDim) (hhW : 0 < hW) (hdW : 0 < dW)
    (hs0 : source0.shape = [lDim, hW, dW])
    (hs1 : source1.shape = [lDim, hW, dW]) :
    fw_view [lDim * 2, hW * dW] (allGatherPrimDimN 0 2 0 [source0, source1]) =
      allGatherPrimDimN 0 2 0
        [fw_view [lDim, hW * dW] source0, fw_view [lDim, hW * dW] source1] := by
  have hhd : 0 < hW * dW := Nat.mul_pos hhW hdW
  have hheadL : (([source0, source1].head?.map (fun t => t.shape)).getD []) =
      [lDim, hW, dW] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hs0]
  have hheadR : ((([fw_view [lDim, hW * dW] source0,
      fw_view [lDim, hW * dW] source1]).head?.map (fun t => t.shape)).getD []) =
      [lDim, hW * dW] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, fw_view_shape']
  have hshapeR : (allGatherPrimDimN 0 2 0
      [fw_view [lDim, hW * dW] source0, fw_view [lDim, hW * dW] source1]).shape =
      [lDim * 2, hW * dW] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, hW * dW] hheadR]
    simp only [List.set, List.getD_cons_zero]
  have hgetL : ∀ r (_ : r < 2),
      ([source0, source1].getD r (zeroTensor [lDim, hW, dW])).shape =
        [lDim, hW, dW] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hs0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
  have hgetR : ∀ r (_ : r < 2),
      ([fw_view [lDim, hW * dW] source0,
        fw_view [lDim, hW * dW] source1].getD r
          (zeroTensor [lDim, hW * dW])).shape = [lDim, hW * dW] := by
    intro r hr
    interval_cases r
    · simp only [List.getD_cons_zero, fw_view_shape']
    · simp only [List.getD_cons_succ, List.getD_cons_zero, fw_view_shape']
  apply Tensor.ext
  · rw [fw_view_shape', hshapeR]
  · intro idx hidx
    rw [fw_view_shape'] at hidx
    have hbound : idx < lDim * 2 * (hW * dW) := by
      simpa only [prodShape_view_2d] using hidx
    set j := idx % (hW * dW) with hjdef
    set row := idx / (hW * dW) with hrowdef
    have hj : j < hW * dW := Nat.mod_lt _ hhd
    have hrow : row < lDim * 2 := by
      rw [hrowdef]
      exact (Nat.div_lt_iff_lt_mul hhd).mpr hbound
    have hidxEq : idx = row * (hW * dW) + j := by
      rw [hrowdef, hjdef]
      exact (Nat.div_add_mod' idx (hW * dW)).symm
    set r := row / lDim with hrdef
    set i := row % lDim with hidef
    have hi : i < lDim := Nat.mod_lt _ hl
    have hr : r < 2 := by
      rw [hrdef]
      exact (Nat.div_lt_iff_lt_mul hl).mpr (by rw [Nat.mul_comm]; exact hrow)
    have hrowEq : row = r * lDim + i := by
      rw [hrdef, hidef]
      exact (Nat.div_add_mod' row lDim).symm
    set jh := j / dW with hjhdef
    set jd := j % dW with hjddef
    have hjd : jd < dW := Nat.mod_lt _ hdW
    have hjh : jh < hW := by
      rw [hjhdef]
      exact (Nat.div_lt_iff_lt_mul hdW).mpr hj
    have hjEq : j = jh * dW + jd := by
      rw [hjhdef, hjddef]
      exact (Nat.div_add_mod' j dW).symm
    -- the flat index rewritten in the two equivalent decompositions
    have hflat3 : idx = ((r * lDim + i) * hW + jh) * dW + jd := by
      rw [hidxEq, hrowEq, hjEq]; ring
    have hflat2 : idx = (r * lDim + i) * (hW * dW) + (i * 0 + j) := by
      rw [hidxEq, hrowEq]; ring
    have hlocal : i * (hW * dW) + j < prodShape [lDim, hW * dW] := by
      rw [prodShape_view_2d]
      calc i * (hW * dW) + j < i * (hW * dW) + (hW * dW) := by omega
        _ = (i + 1) * (hW * dW) := by ring
        _ ≤ lDim * (hW * dW) := Nat.mul_le_mul_right _ hi
    -- LHS
    rw [fw_view_valAt _ _ _ (by rw [prodShape_view_2d]; exact hbound)]
    rw [show idx = ((r * lDim + i) * hW + jh) * dW + jd from hflat3]
    rw [allGatherPrimDimN0_valAt_3D 2 lDim hW dW [source0, source1]
      (by decide) hl hhW hdW hheadL hgetL r hr i hi jh hjh jd hjd]
    -- RHS
    rw [show ((r * lDim + i) * hW + jh) * dW + jd
        = (r * lDim + i) * (hW * dW) + j from by rw [hjEq]; ring]
    rw [allGatherPrimDimN0_valAt 2 lDim (hW * dW)
      [fw_view [lDim, hW * dW] source0, fw_view [lDim, hW * dW] source1]
      (by decide) hl hhd hheadR hgetR r hr i hi j hj]
    -- both sides now read the same source shard at the same flat offset
    have hsrc : ∀ (a : Tensor), a.shape = [lDim, hW, dW] →
        valAt a ((i * hW + jh) * dW + jd) = valAt a (i * (hW * dW) + j) := by
      intro a _
      rw [show (i * hW + jh) * dW + jd = i * (hW * dW) + (jh * dW + jd) from by ring,
        ← hjEq]
    interval_cases r
    · simp only [List.getD_cons_zero]
      rw [fw_view_valAt _ _ _ hlocal]
      exact hsrc source0 hs0
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [fw_view_valAt _ _ _ hlocal]
      exact hsrc source1 hs1

/-! ## `fw_view` commutes with the faithful CP2 shuffle -/

/-- The faithful CP2 shuffle only moves whole rows: its index arithmetic uses
`chunk = shape.getD 0 0 = lDim` and `hiddenStride = prodShape shape.tail = hW * dW`,
both of which are invariant under `[lDim, hW, dW] ↦ [lDim, hW * dW]`.  Hence the
merge commutes with the shuffle on every rank. -/
theorem fw_view_shuffle_collective_cp2
    (source0 source1 : Tensor) (cu : List Nat) (lDim hW dW rank : Nat)
    (hl : 0 < lDim) (hhW : 0 < hW) (hdW : 0 < dW) (hrank : rank < 2)
    (hs0 : source0.shape = [lDim, hW, dW])
    (hs1 : source1.shape = [lDim, hW, dW]) :
    fw_view [lDim, hW * dW]
        (fw_maybe_shuffle_collective [source0, source1] cu 2 rank) =
      fw_maybe_shuffle_collective
        [fw_view [lDim, hW * dW] source0, fw_view [lDim, hW * dW] source1]
        cu 2 rank := by
  have hhd : 0 < hW * dW := Nat.mul_pos hhW hdW
  have hlocal : ([source0, source1].getD rank (zeroTensor [])).shape =
      [lDim, hW, dW] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hs0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
  have hlocalV : ([fw_view [lDim, hW * dW] source0,
      fw_view [lDim, hW * dW] source1].getD rank (zeroTensor [])).shape =
      [lDim, hW * dW] := by
    interval_cases rank
    · simp only [List.getD_cons_zero, fw_view_shape']
    · simp only [List.getD_cons_succ, List.getD_cons_zero, fw_view_shape']
  apply Tensor.ext
  · rw [fw_view_shape', fw_maybe_shuffle_collective_shape, hlocalV]
  · intro idx hidx
    rw [fw_view_shape'] at hidx
    have hbound : idx < lDim * (hW * dW) := by
      simpa only [prodShape_view_2d] using hidx
    rw [fw_view_valAt _ _ _ (by rw [prodShape_view_2d]; exact hbound)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocal, prodShape_shard_3d]; exact hbound)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocalV, prodShape_view_2d]; exact hbound)]
    simp only [hlocal, hlocalV, List.tail_cons, prodShape, List.foldl,
      Nat.one_mul, Nat.mul_one, List.getD_cons_zero]
    -- identical index arithmetic on both sides; only the source list differs
    unfold gatherFromRank
    set g := zigzagPos cu 2 rank (idx / (hW * dW)) with hg
    set off := g % lDim * (hW * dW) + idx % (hW * dW) with hoff
    by_cases h0 : g / lDim = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      by_cases hb : off < prodShape [lDim, hW * dW]
      · exact (fw_view_valAt _ source0 off hb).symm
      · rw [valAt, valAt]
        rw [prodShape_view_2d] at hb
        rw [dif_neg (by rw [hs0, prodShape_shard_3d]; exact hb),
          dif_neg (by rw [fw_view_shape', prodShape_view_2d]; exact hb)]
    · by_cases h1 : g / lDim = 1
      · rw [h1]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        by_cases hb : off < prodShape [lDim, hW * dW]
        · exact (fw_view_valAt _ source1 off hb).symm
        · rw [valAt, valAt]
          rw [prodShape_view_2d] at hb
          rw [dif_neg (by rw [hs1, prodShape_shard_3d]; exact hb),
            dif_neg (by rw [fw_view_shape', prodShape_view_2d]; exact hb)]
      · have hge : ∀ n : Nat, ¬ n = 0 → ¬ n = 1 → 2 ≤ n := by intro n a b; omega
        have hnot : 2 ≤ g / lDim := hge _ h0 h1
        have hgetA : [source0, source1].getD (g / lDim) (zeroTensor []) =
            zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hnot),
            Option.getD_none]
        have hgetB : [fw_view [lDim, hW * dW] source0,
            fw_view [lDim, hW * dW] source1].getD (g / lDim) (zeroTensor []) =
            zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hnot),
            Option.getD_none]
        simp only [hgetA, hgetB]

/-! ## Metadata well-formedness transports along the merge -/

/-- Merging the trailing axes of both CP2 source shards preserves packed-sequence
well-formedness: the contract only mentions metadata and the dim-0 token count,
which the merge leaves untouched. -/
theorem ZigzagCuWF.view_3d_to_2d_cp2
    (cu : List Nat) (source0 source1 : Tensor) (lDim hW dW : Nat)
    (hwf : ZigzagCuWF cu [source0, source1] 2)
    (hs0 : source0.shape = [lDim, hW, dW])
    (hs1 : source1.shape = [lDim, hW, dW]) :
    ZigzagCuWF cu
      [fw_view [lDim, hW * dW] source0, fw_view [lDim, hW * dW] source1] 2 := by
  refine ⟨hwf.cp_pos, rfl, hwf.cu_starts_zero, hwf.cu_has_endpoint,
    hwf.monotone, hwf.divisible, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;>
      · rw [fw_view_shape']
        exact List.cons_ne_nil _ _
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rfl
    · simp only [List.getD_cons_zero, fw_view_shape']
  · have h := hwf.local_tokens
    simp only [List.getD_cons_zero, hs0] at h
    simpa only [List.getD_cons_zero, fw_view_shape'] using h

namespace Zigzag2Rel

/-- Row-local reshape/view `[lDim, hW, dW] ↦ [lDim, hW * dW]` preserves the CP2
zigzag layout relation.  This models the graph's `FW_reshape` node, whose target
shape is parameterised per shard (`[4096, 1024]` single-machine vs `[2048, 1024]`
per rank). -/
theorem view_3d_to_2d
    {full z0 z1 cu : Tensor} (lDim hW dW : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, hW, dW] [lDim, hW, dW])
    (hl : 0 < lDim) (hhW : 0 < hW) (hdW : 0 < dW) :
    Zigzag2Rel
      (fw_view [lDim * 2, hW * dW] full)
      (fw_view [lDim, hW * dW] z0)
      (fw_view [lDim, hW * dW] z1)
      cu [lDim * 2, hW * dW] [lDim, hW * dW] := by
  rcases hrel with ⟨source0, source1, hs⟩
  have hs0 : source0.shape = [lDim, hW, dW] := hs.source0_shape
  have hs1 : source1.shape = [lDim, hW, dW] := hs.source1_shape
  refine ⟨fw_view [lDim, hW * dW] source0, fw_view [lDim, hW * dW] source1,
    ?_, ?_, ?_, fw_view_shape' _ _, fw_view_shape' _ _, fw_view_shape' _ _,
    fw_view_shape' _ _, fw_view_shape' _ _,
    ZigzagCuWF.view_3d_to_2d_cp2 _ source0 source1 lDim hW dW hs.cu_wf hs0 hs1⟩
  · rw [hs.full_value]
    exact fw_view_allGather0_commute_cp2 source0 source1 lDim hW dW hl hhW hdW hs0 hs1
  · rw [hs.rank0_value]
    exact fw_view_shuffle_collective_cp2 source0 source1 (decodeCuSeqlens cu)
      lDim hW dW 0 hl hhW hdW (by decide) hs0 hs1
  · rw [hs.rank1_value]
    exact fw_view_shuffle_collective_cp2 source0 source1 (decodeCuSeqlens cu)
      lDim hW dW 1 hl hhW hdW (by decide) hs0 hs1

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
