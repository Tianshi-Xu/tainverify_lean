/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Broadcast multiplication preserves the CP2 zigzag layout relation

SM node 533 of the YOCO/MoE graph is `FW_mul ins=[5370, 5383] outs=[5384]` with

* `5370 : [4096, 1]`   (a per-token gate, produced by `FW_sigmoid`)
* `5383 : [4096, 1024]`
* `5384 : [4096, 1024]`

i.e. a **broadcast** multiply `[lDim, 1] ⊗ [lDim, d] → [lDim, d]`.  The already
proved `Zigzag2Rel.mul` (`denote/yoco_goals/ZigzagElemwiseRel.lean`) demands both
operands to have the *same* shape `[lDim, d]`, so it does not apply.  This file
supplies the broadcast variant.

The key observation is that the broadcast happens purely in the **column**
direction (one column is replicated to `d` columns) while the zigzag collective
only permutes **rows** (whole `hiddenStride`-sized slots).  The two are
orthogonal, so the very same three-step recipe used for the same-shape case goes
through:

* `mulBC_allGather0_commute_cp2` — commutation with the ordinary dim-0 gather,
* `mulBC_shuffle_collective_cp2` — commutation with `fw_maybe_shuffle_collective`,
* `ZigzagCuWF_mulBC_cp2`        — transport of the metadata well-formedness.

Note the one genuinely new ingredient: the two operands are shuffled with
*different* `hiddenStride`s (`1` for the gate, `d` for the payload), yet both
resolve the same token index `idx / d` and hence the same `zigzagPos`.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

namespace ZigzagBroadcastMul

open ZigzagElemwise

/-! ## Broadcast reads -/

/-- A `broadcastValAtShape` read of a single-column `[a, 1]` tensor against the
broadcast output shape `[a, b]` collapses to a plain read at the *row* index. -/
theorem broadcastValAtShape_col1 (t : Tensor) (a b k : Nat)
    (ht : t.shape = [a, 1]) (hb : 0 < b) (hk : k < a * b) :
    broadcastValAtShape [a, b] t k = valAt t (k / b) := by
  have hmi : alignedMultiIndex [a, b] [a, 1] k =
      [if a = 1 then 0 else k / b, 0] := by
    simp only [alignedMultiIndex, List.length_cons, List.length_nil,
      Nat.sub_self, List.drop_zero, flatToMulti_2d a b k hb,
      List.ofFn_succ, List.ofFn_zero, Fin.isValue,
      List.getD_cons_zero, List.getD_cons_succ]
    rfl
  have hflat : multiToFlat [a, 1] (alignedMultiIndex [a, b] [a, 1] k) =
      (if a = 1 then 0 else k / b) := by
    rw [hmi]
    show (if a = 1 then 0 else k / b) * prodShape ([1] : Shape) +
      multiToFlat [1] [0] = _
    have h1 : prodShape ([1] : Shape) = 1 := by
      simp only [prodShape, List.foldl, Nat.one_mul]
    have h2 : multiToFlat ([1] : Shape) [0] = 0 := by
      show 0 * prodShape ([] : Shape) + multiToFlat ([] : Shape) [] = 0
      show 0 * 1 + 0 = 0
      omega
    rw [h1, h2, Nat.mul_one, Nat.add_zero]
  have hif : (if a = 1 then 0 else k / b) = k / b := by
    by_cases ha : a = 1
    · subst ha
      rw [if_pos rfl, Nat.one_mul] at *
      exact (Nat.div_eq_of_lt hk).symm
    · rw [if_neg ha]
  show valAt t (multiToFlat t.shape (alignedMultiIndex [a, b] t.shape k)) = _
  rw [ht, hflat, hif]

/-! ## Shape and value contract for the broadcast product -/

/-- `[a, 1] ⊗ [a, b]` broadcasts to `[a, b]`. -/
theorem elemwiseMul_shape_col1 (x y : Tensor) (a b : Nat)
    (hx : x.shape = [a, 1]) (hy : y.shape = [a, b]) (hb : 0 < b) :
    (elemwiseMul x y).shape = [a, b] := by
  have hb1 : 1 ≤ b := hb
  unfold elemwiseMul Tensor.mkShape
  change outShape2 x y = [a, b]
  simp only [outShape2, hx, hy, List.length_cons, List.length_nil,
    Nat.max_self, Nat.sub_self, List.replicate, List.nil_append,
    List.zipWith, Nat.max_self, Nat.max_eq_right hb1]

/-- Value contract for the broadcast product: the single-column operand is read
at the row index `idx / b`, the wide operand at `idx`. -/
theorem elemwiseMul_valAt_col1 (x y : Tensor) (a b idx : Nat)
    (hx : x.shape = [a, 1]) (hy : y.shape = [a, b]) (hb : 0 < b)
    (hidx : idx < a * b) :
    valAt (elemwiseMul x y) idx = valAt x (idx / b) * valAt y idx := by
  have hb1 : 1 ≤ b := hb
  have hout : (elemwiseMul x y).shape = [a, b] :=
    elemwiseMul_shape_col1 x y a b hx hy hb
  have hos : outShape2 x y = [a, b] := by
    simp only [outShape2, hx, hy, List.length_cons, List.length_nil,
      Nat.max_self, Nat.sub_self, List.replicate, List.nil_append,
      List.zipWith, Nat.max_self, Nat.max_eq_right hb1]
  have hstep : valAt (elemwiseMul x y) idx =
      broadcastValAtShape (outShape2 x y) x idx *
        broadcastValAtShape (outShape2 x y) y idx := by
    rw [valAt_of_lt _ _ (by rw [hout, prodShape_2d']; exact hidx)]
    rfl
  rw [hstep, hos, broadcastValAtShape_col1 x a b idx hx hb hidx,
    broadcastValAtShape_self_2d y a b idx hy hb hidx]

/-! ## (1) Commutation with the ordinary CP2 dim-0 all-gather -/

theorem mulBC_allGather0_commute_cp2
    (a0 a1 b0 b1 : Tensor) (lDim d : Nat) (hl : 0 < lDim) (hd : 0 < d)
    (ha0 : a0.shape = [lDim, 1]) (ha1 : a1.shape = [lDim, 1])
    (hb0 : b0.shape = [lDim, d]) (hb1 : b1.shape = [lDim, d]) :
    elemwiseMul (allGatherPrimDimN 0 2 0 [a0, a1])
        (allGatherPrimDimN 0 2 0 [b0, b1]) =
      allGatherPrimDimN 0 2 0 [elemwiseMul a0 b0, elemwiseMul a1 b1] := by
  have hs0 : (elemwiseMul a0 b0).shape = [lDim, d] :=
    elemwiseMul_shape_col1 a0 b0 lDim d ha0 hb0 hd
  have hs1 : (elemwiseMul a1 b1).shape = [lDim, d] :=
    elemwiseMul_shape_col1 a1 b1 lDim d ha1 hb1 hd
  have hheadA : (([a0, a1].head?.map (fun t => t.shape)).getD []) = [lDim, 1] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, ha0]
  have hheadB : (([b0, b1].head?.map (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hb0]
  have hheadS : (([elemwiseMul a0 b0, elemwiseMul a1 b1].head?.map
      (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hs0]
  have hgetA : ∀ r (_ : r < 2),
      ([a0, a1].getD r (zeroTensor [lDim, 1])).shape = [lDim, 1] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using ha0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using ha1
  have hgetB : ∀ r (_ : r < 2),
      ([b0, b1].getD r (zeroTensor [lDim, d])).shape = [lDim, d] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hb0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hb1
  have hgetS : ∀ r (_ : r < 2),
      ([elemwiseMul a0 b0, elemwiseMul a1 b1].getD r
        (zeroTensor [lDim, d])).shape = [lDim, d] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hs0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
  have hshapeA : (allGatherPrimDimN 0 2 0 [a0, a1]).shape = [lDim * 2, 1] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, 1] hheadA]
    simp only [List.set, List.getD_cons_zero]
  have hshapeB : (allGatherPrimDimN 0 2 0 [b0, b1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadB]
    simp only [List.set, List.getD_cons_zero]
  have hshapeS : (allGatherPrimDimN 0 2 0
      [elemwiseMul a0 b0, elemwiseMul a1 b1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadS]
    simp only [List.set, List.getD_cons_zero]
  have hlhsShape : (elemwiseMul (allGatherPrimDimN 0 2 0 [a0, a1])
      (allGatherPrimDimN 0 2 0 [b0, b1])).shape = [lDim * 2, d] :=
    elemwiseMul_shape_col1 _ _ (lDim * 2) d hshapeA hshapeB hd
  refine Tensor.ext ?_ ?_
  · rw [hlhsShape, hshapeS]
  · intro idx hidx
    rw [hlhsShape, prodShape_2d'] at hidx
    set j := idx % d with hjdef
    set row := idx / d with hrowdef
    have hj : j < d := Nat.mod_lt _ hd
    have hrow : row < lDim * 2 := by
      rw [hrowdef]; exact (Nat.div_lt_iff_lt_mul hd).mpr hidx
    have hidxEq : idx = row * d + j := by
      rw [hrowdef, hjdef]; exact (Nat.div_add_mod' idx d).symm
    set r := row / lDim with hrdef
    set i := row % lDim with hidef
    have hi : i < lDim := Nat.mod_lt _ hl
    have hr : r < 2 := by
      rw [hrdef]
      exact (Nat.div_lt_iff_lt_mul hl).mpr (by rw [Nat.mul_comm]; exact hrow)
    have hrowEq : row = r * lDim + i := by
      rw [hrdef, hidef]; exact (Nat.div_add_mod' row lDim).symm
    have hflat : idx = (r * lDim + i) * d + j := by rw [hidxEq, hrowEq]
    have hloc : i * d + j < lDim * d := by
      calc i * d + j < i * d + d := by omega
        _ = (i + 1) * d := by ring
        _ ≤ lDim * d := Nat.mul_le_mul_right _ hi
    rw [elemwiseMul_valAt_col1 _ _ (lDim * 2) d idx hshapeA hshapeB hd hidx]
    have hdivEq : idx / d = r * lDim + i := by rw [← hrowdef, hrowEq]
    rw [hdivEq, hflat]
    -- gather on the wide operand and on the product
    rw [allGatherPrimDimN0_valAt 2 lDim d [b0, b1] (by decide) hl hd
      hheadB hgetB r hr i hi j hj]
    rw [allGatherPrimDimN0_valAt 2 lDim d [elemwiseMul a0 b0, elemwiseMul a1 b1]
      (by decide) hl hd hheadS hgetS r hr i hi j hj]
    -- gather on the single-column operand: rewrite `n` as `n * 1 + 0`
    conv_lhs => lhs; rw [show r * lDim + i = (r * lDim + i) * 1 + 0 from by ring]
    rw [allGatherPrimDimN0_valAt 2 lDim 1 [a0, a1] (by decide) hl (by omega)
      hheadA hgetA r hr i hi 0 (by omega)]
    have hlocDiv : (i * d + j) / d = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj,
        Nat.zero_add]
    interval_cases r
    · simp only [List.getD_cons_zero]
      rw [elemwiseMul_valAt_col1 a0 b0 lDim d (i * d + j) ha0 hb0 hd hloc,
        hlocDiv, Nat.mul_one, Nat.add_zero]
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [elemwiseMul_valAt_col1 a1 b1 lDim d (i * d + j) ha1 hb1 hd hloc,
        hlocDiv, Nat.mul_one, Nat.add_zero]

/-! ## (2) Commutation with the faithful CP2 zigzag shuffle -/

theorem mulBC_shuffle_collective_cp2
    (a0 a1 b0 b1 : Tensor) (cu : List Nat) (lDim d rank : Nat)
    (hl : 0 < lDim) (hd : 0 < d) (hrank : rank < 2)
    (ha0 : a0.shape = [lDim, 1]) (ha1 : a1.shape = [lDim, 1])
    (hb0 : b0.shape = [lDim, d]) (hb1 : b1.shape = [lDim, d]) :
    elemwiseMul (fw_maybe_shuffle_collective [a0, a1] cu 2 rank)
        (fw_maybe_shuffle_collective [b0, b1] cu 2 rank) =
      fw_maybe_shuffle_collective
        [elemwiseMul a0 b0, elemwiseMul a1 b1] cu 2 rank := by
  have hs0 : (elemwiseMul a0 b0).shape = [lDim, d] :=
    elemwiseMul_shape_col1 a0 b0 lDim d ha0 hb0 hd
  have hs1 : (elemwiseMul a1 b1).shape = [lDim, d] :=
    elemwiseMul_shape_col1 a1 b1 lDim d ha1 hb1 hd
  have hlocA : ([a0, a1].getD rank (zeroTensor [])).shape = [lDim, 1] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using ha0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using ha1
  have hlocB : ([b0, b1].getD rank (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hb0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hb1
  have hlocS : ([elemwiseMul a0 b0, elemwiseMul a1 b1].getD rank
      (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hs0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
  have hshA : (fw_maybe_shuffle_collective [a0, a1] cu 2 rank).shape =
      [lDim, 1] := by rw [fw_maybe_shuffle_collective_shape, hlocA]
  have hshB : (fw_maybe_shuffle_collective [b0, b1] cu 2 rank).shape =
      [lDim, d] := by rw [fw_maybe_shuffle_collective_shape, hlocB]
  have hshS : (fw_maybe_shuffle_collective
      [elemwiseMul a0 b0, elemwiseMul a1 b1] cu 2 rank).shape =
      [lDim, d] := by rw [fw_maybe_shuffle_collective_shape, hlocS]
  have hlhsShape : (elemwiseMul (fw_maybe_shuffle_collective [a0, a1] cu 2 rank)
      (fw_maybe_shuffle_collective [b0, b1] cu 2 rank)).shape = [lDim, d] :=
    elemwiseMul_shape_col1 _ _ lDim d hshA hshB hd
  refine Tensor.ext ?_ ?_
  · rw [hlhsShape, hshS]
  · intro idx hidx
    rw [hlhsShape, prodShape_2d'] at hidx
    have hrowLt : idx / d < lDim := (Nat.div_lt_iff_lt_mul hd).mpr hidx
    rw [elemwiseMul_valAt_col1 _ _ lDim d idx hshA hshB hd hidx]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocA, prodShape_2d', Nat.mul_one]; exact hrowLt)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocB, prodShape_2d']; exact hidx)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocS, prodShape_2d']; exact hidx)]
    simp only [hlocA, hlocB, hlocS, List.tail_cons, prodShape, List.foldl,
      Nat.one_mul, List.getD_cons_zero, Nat.div_one, Nat.mod_one]
    unfold gatherFromRank
    set g := zigzagPos cu 2 rank (idx / d) with hg
    set off := g % lDim * d + idx % d with hoff
    have hoffLt : off < lDim * d := by
      have h1 : g % lDim < lDim := Nat.mod_lt _ hl
      have h2 : idx % d < d := Nat.mod_lt _ hd
      calc off < g % lDim * d + d := by omega
        _ = (g % lDim + 1) * d := by ring
        _ ≤ lDim * d := Nat.mul_le_mul_right _ h1
    have hoffDiv : off / d = g % lDim := by
      rw [hoff, Nat.add_comm, Nat.add_mul_div_right _ _ hd,
        Nat.div_eq_of_lt (Nat.mod_lt _ hd), Nat.zero_add]
    by_cases h0 : g / lDim = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      rw [elemwiseMul_valAt_col1 a0 b0 lDim d off ha0 hb0 hd hoffLt, hoffDiv,
        Nat.mul_one, Nat.add_zero]
    · by_cases h1 : g / lDim = 1
      · rw [h1]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        rw [elemwiseMul_valAt_col1 a1 b1 lDim d off ha1 hb1 hd hoffLt, hoffDiv,
          Nat.mul_one, Nat.add_zero]
      · have hnot : 2 ≤ g / lDim := two_le_of_ne_zero_ne_one _ h0 h1
        have hgA : [a0, a1].getD (g / lDim) (zeroTensor []) = zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        have hgB : [b0, b1].getD (g / lDim) (zeroTensor []) = zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        have hgS : [elemwiseMul a0 b0, elemwiseMul a1 b1].getD (g / lDim)
            (zeroTensor []) = zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        simp only [hgA, hgB, hgS, valAt_zeroTensor_empty, mul_zero]

/-! ## (3) Metadata well-formedness transport -/

theorem ZigzagCuWF_mulBC_cp2
    (cu : List Nat) (a0 a1 b0 b1 : Tensor) (lDim d : Nat) (hd : 0 < d)
    (hwf : ZigzagCuWF cu [a0, a1] 2)
    (ha0 : a0.shape = [lDim, 1]) (ha1 : a1.shape = [lDim, 1])
    (hb0 : b0.shape = [lDim, d]) (hb1 : b1.shape = [lDim, d]) :
    ZigzagCuWF cu [elemwiseMul a0 b0, elemwiseMul a1 b1] 2 := by
  have hs0 : (elemwiseMul a0 b0).shape = [lDim, d] :=
    elemwiseMul_shape_col1 a0 b0 lDim d ha0 hb0 hd
  have hs1 : (elemwiseMul a1 b1).shape = [lDim, d] :=
    elemwiseMul_shape_col1 a1 b1 lDim d ha1 hb1 hd
  refine ⟨hwf.cp_pos, rfl, hwf.cu_starts_zero, hwf.cu_has_endpoint,
    hwf.monotone, hwf.divisible, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hs0]; exact List.cons_ne_nil _ _
    · rw [hs1]; exact List.cons_ne_nil _ _
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rfl
    · simp only [List.getD_cons_zero, hs0, hs1]
  · have h := hwf.local_tokens
    simp only [List.getD_cons_zero, ha0] at h
    simpa only [List.getD_cons_zero, hs0] using h

end ZigzagBroadcastMul

open ZigzagBroadcastMul

namespace Zigzag2Rel

/-- **Broadcast multiplication preserves the CP2 zigzag layout relation.**

`OpName.FW_mul` on a single-column gate `[lDim*2, 1]` and a wide payload
`[lDim*2, d]` (SM node 533: `5370 : [4096,1]`, `5383 : [4096,1024]`,
`5384 : [4096,1024]`; PM nodes 1128/1129 at `[2048,1]`/`[2048,1024]`)
stays in CP2 zigzag layout with the same `cu` metadata. -/
theorem mul_broadcast_col1
    {fullA zA0 zA1 fullB zB0 zB1 cu : Tensor} (lDim d : Nat)
    (hA : Zigzag2Rel fullA zA0 zA1 cu [lDim * 2, 1] [lDim, 1])
    (hB : Zigzag2Rel fullB zB0 zB1 cu [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    Zigzag2Rel (elemwiseMul fullA fullB) (elemwiseMul zA0 zB0)
      (elemwiseMul zA1 zB1) cu [lDim * 2, d] [lDim, d] := by
  rcases hA with ⟨a0, a1, hAs⟩
  rcases hB with ⟨b0, b1, hBs⟩
  have ha0 : a0.shape = [lDim, 1] := hAs.source0_shape
  have ha1 : a1.shape = [lDim, 1] := hAs.source1_shape
  have hb0 : b0.shape = [lDim, d] := hBs.source0_shape
  have hb1 : b1.shape = [lDim, d] := hBs.source1_shape
  refine ⟨elemwiseMul a0 b0, elemwiseMul a1 b1, ?_, ?_, ?_, ?_,
    elemwiseMul_shape_col1 a0 b0 lDim d ha0 hb0 hd,
    elemwiseMul_shape_col1 a1 b1 lDim d ha1 hb1 hd, ?_, ?_,
    ZigzagCuWF_mulBC_cp2 (decodeCuSeqlens cu) a0 a1 b0 b1 lDim d hd
      hAs.cu_wf ha0 ha1 hb0 hb1⟩
  · rw [hAs.full_value, hBs.full_value]
    exact mulBC_allGather0_commute_cp2 a0 a1 b0 b1 lDim d hl hd
      ha0 ha1 hb0 hb1
  · rw [hAs.rank0_value, hBs.rank0_value]
    exact mulBC_shuffle_collective_cp2 a0 a1 b0 b1 (decodeCuSeqlens cu)
      lDim d 0 hl hd (by decide) ha0 ha1 hb0 hb1
  · rw [hAs.rank1_value, hBs.rank1_value]
    exact mulBC_shuffle_collective_cp2 a0 a1 b0 b1 (decodeCuSeqlens cu)
      lDim d 1 hl hd (by decide) ha0 ha1 hb0 hb1
  · exact elemwiseMul_shape_col1 fullA fullB (lDim * 2) d
      hAs.full_shape hBs.full_shape hd
  · exact elemwiseMul_shape_col1 zA0 zB0 lDim d
      hAs.rank0_shape hBs.rank0_shape hd
  · exact elemwiseMul_shape_col1 zA1 zB1 lDim d
      hAs.rank1_shape hBs.rank1_shape hd

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
