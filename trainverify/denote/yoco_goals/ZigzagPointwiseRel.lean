/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagLayoutRel

/-!
# Pointwise / identity-like operators preserve the CP2 zigzag layout relation

Three propagation lemmas for `Zigzag2Rel`:

* `Zigzag2Rel.view_id` — an *identity* `fw_view` (target shape equal to the input
  shape).  This models SM node 506 `FW_reshape ins [5348] outs [5349]
  params [4096, 1024]`, where tensor 5348 already has shape `[4096, 1024]`.
* `Zigzag2Rel.fw_float` — `FW_float` is *literally the identity* in the model
  (`evalOp_fw_float : evalOp _ _ "OpName.FW_float" params [x] = [x]`).  There is
  no separate tensor-level `fw_float` definition in the core library, so the
  lemma is phrased at the `evalOp` level, which is exactly the form the graph
  bridge consumes.
* `Zigzag2Rel.add` — elementwise addition (`OpName.FW_add`, semantically
  `elemwiseAdd`) of two zigzag-laid-out tensors that share the *same* `cu`
  metadata.  This is the residual connection: SM node 510
  `FW_add ins [8143, 5353] outs [5354]`, PM nodes 1078/1079.

The `add` case is the substantial one: `Zigzag2Rel` is existentially quantified
over the ordinary contiguous source shards, so the two hypotheses supply their
own witnesses `(a0, a1)` and `(b0, b1)`; we must show `elemwiseAdd a_i b_i` is a
valid witness for the sum.  Both required commutations hold because addition is
pointwise while the CP collectives only *move whole rows*:

* the dim-0 all-gather is a flat concatenation, so a pointwise binary operator
  distributes over it;
* the faithful zigzag shuffle reads `gatherFromRank`, i.e. it copies one flat
  slot of one source shard into one flat slot of the output, so a pointwise
  binary operator distributes over it too.

There is no pre-existing `fw_add … allGather` commutation lemma at this
generality in the core library: `denote/Denote.lean` only carries the concrete
`[1, 8, 32]` shape instances (`fw_add_split_dim1/2_4_1_8_32`) and
`denote/yoco_goals/Pattern_1.lean` carries the fixed `[2048, 1024]` /
`[4096, 1024]` instances.  We therefore prove the shape-generic 2D versions
here.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-! ## Elementary `fw_view` facts (identity case) -/

/-- `fw_view` produces exactly the requested shape. -/
theorem fw_view_shape_eq (targetShape : Shape) (x : Tensor) :
    (fw_view targetShape x).shape = targetShape := rfl

/-- In range, `fw_view` is the identity on flat data. -/
theorem fw_view_valAt_eq (targetShape : Shape) (x : Tensor) (m : Nat)
    (hm : m < prodShape targetShape) :
    valAt (fw_view targetShape x) m = valAt x m := by
  unfold fw_view
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hm)]
  rfl

/-- A `fw_view` whose target shape is the input's own shape is the identity. -/
theorem fw_view_id (x : Tensor) (targetShape : Shape)
    (hx : x.shape = targetShape) :
    fw_view targetShape x = x := by
  refine Tensor.ext ?_ ?_
  · rw [fw_view_shape_eq, hx]
  · intro idx hidx
    rw [fw_view_shape_eq] at hidx
    exact fw_view_valAt_eq targetShape x idx hidx

/-! ## Elementary `elemwiseAdd` facts -/

theorem prodShape_2d (a b : Nat) : prodShape [a, b] = a * b := by
  simp only [prodShape, List.foldl, Nat.one_mul]

/-- `flatToMulti` on a 2D shape. -/
theorem flatToMulti_2d (a b k : Nat) (hb : 0 < b) :
    flatToMulti [a, b] k = [k / b, k % b] := by
  have hb' : prodShape ([b] : Shape) = b := by
    simp only [prodShape, List.foldl, Nat.one_mul]
  have hbne : prodShape ([b] : Shape) ≠ 0 := by rw [hb']; omega
  have hone : prodShape ([] : Shape) = 1 := rfl
  have hinner : ∀ m : Nat, flatToMulti [b] m = [m] := by
    intro m
    show (let stride := prodShape ([] : Shape)
          if stride = 0 then 0 :: flatToMulti [] 0
          else (m / stride) :: flatToMulti [] (m % stride)) = _
    dsimp only []
    rw [hone, if_neg (by omega), Nat.div_one]
    rfl
  show (let stride := prodShape ([b] : Shape)
        if stride = 0 then 0 :: flatToMulti [b] 0
        else (k / stride) :: flatToMulti [b] (k % stride)) = _
  dsimp only []
  rw [if_neg hbne, hb', hinner]

/-- A `broadcastValAtShape` read at the tensor's own 2D shape is a plain read. -/
theorem broadcastValAtShape_self_2d (t : Tensor) (a b k : Nat)
    (ht : t.shape = [a, b]) (hb : 0 < b) (hk : k < a * b) :
    broadcastValAtShape [a, b] t k = valAt t k := by
  have hmi : alignedMultiIndex [a, b] [a, b] k =
      [if a = 1 then 0 else k / b, if b = 1 then 0 else k % b] := by
    simp only [alignedMultiIndex, Nat.sub_self, List.drop_zero,
      flatToMulti_2d a b k hb, List.ofFn_succ, List.ofFn_zero, Fin.isValue,
      List.getD_cons_zero, List.getD_cons_succ]
    rfl
  have hflat : multiToFlat [a, b] (alignedMultiIndex [a, b] [a, b] k) = k := by
    rw [hmi]
    show (if a = 1 then 0 else k / b) * prodShape [b] +
      multiToFlat [b] [if b = 1 then 0 else k % b] = k
    have hb' : prodShape ([b] : Shape) = b := by
      simp only [prodShape, List.foldl, Nat.one_mul]
    have hin : multiToFlat [b] [if b = 1 then 0 else k % b] =
        (if b = 1 then 0 else k % b) := by
      show (if b = 1 then 0 else k % b) * prodShape ([] : Shape) +
        multiToFlat [] [] = _
      show (if b = 1 then 0 else k % b) * 1 + 0 = _
      omega
    rw [hb', hin]
    by_cases hb1 : b = 1
    · subst hb1
      rw [if_pos rfl, Nat.mul_one, Nat.add_zero]
      by_cases ha1 : a = 1
      · subst ha1; rw [if_pos rfl]; omega
      · rw [if_neg ha1, Nat.div_one]
    · rw [if_neg hb1]
      by_cases ha1 : a = 1
      · subst ha1
        rw [if_pos rfl, Nat.zero_mul, Nat.zero_add, Nat.one_mul] at *
        rw [Nat.mod_eq_of_lt hk]
      · rw [if_neg ha1]
        exact Nat.div_add_mod' k b
  show valAt t (multiToFlat t.shape (alignedMultiIndex [a, b] t.shape k)) = valAt t k
  rw [ht, hflat]

/-- Same-shape 2D elementwise add is pointwise on flat indices. -/
theorem elemwiseAdd_valAt_2d (x y : Tensor) (a b idx : Nat)
    (hx : x.shape = [a, b]) (hy : y.shape = [a, b]) (hb : 0 < b)
    (hidx : idx < a * b) :
    valAt (elemwiseAdd x y) idx = valAt x idx + valAt y idx := by
  have hout : (elemwiseAdd x y).shape = [a, b] :=
    elemwiseAdd_shape_of_shapes x y [a, b] hx hy
  have hos : outShape2 x y = [a, b] := by
    simp only [outShape2, hx, hy, List.length_cons, List.length_nil,
      Nat.max_self, Nat.sub_self, List.replicate, List.nil_append,
      List.zipWith, Nat.max_self]
  have hstep : valAt (elemwiseAdd x y) idx =
      broadcastValAtShape (outShape2 x y) x idx +
        broadcastValAtShape (outShape2 x y) y idx := by
    rw [valAt_of_lt _ _ (by rw [hout, prodShape_2d]; exact hidx)]
    rfl
  rw [hstep, hos, broadcastValAtShape_self_2d x a b idx hx hb hidx,
    broadcastValAtShape_self_2d y a b idx hy hb hidx]

/-! ## `elemwiseAdd` commutes with the CP2 dim-0 all-gather -/

/-- Pointwise addition distributes over the ordinary dim-0 all-gather. -/
theorem elemwiseAdd_allGather0_commute_cp2
    (a0 a1 b0 b1 : Tensor) (lDim d : Nat)
    (hl : 0 < lDim) (hd : 0 < d)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d])
    (hb0 : b0.shape = [lDim, d]) (hb1 : b1.shape = [lDim, d]) :
    elemwiseAdd (allGatherPrimDimN 0 2 0 [a0, a1])
        (allGatherPrimDimN 0 2 0 [b0, b1]) =
      allGatherPrimDimN 0 2 0 [elemwiseAdd a0 b0, elemwiseAdd a1 b1] := by
  have hheadA : (([a0, a1].head?.map (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, ha0]
  have hheadB : (([b0, b1].head?.map (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hb0]
  have hsum0 : (elemwiseAdd a0 b0).shape = [lDim, d] :=
    elemwiseAdd_shape_of_shapes a0 b0 [lDim, d] ha0 hb0
  have hsum1 : (elemwiseAdd a1 b1).shape = [lDim, d] :=
    elemwiseAdd_shape_of_shapes a1 b1 [lDim, d] ha1 hb1
  have hheadS : (([elemwiseAdd a0 b0, elemwiseAdd a1 b1].head?.map
      (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hsum0]
  have hgetA : ∀ r (_ : r < 2),
      ([a0, a1].getD r (zeroTensor [lDim, d])).shape = [lDim, d] := by
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
      ([elemwiseAdd a0 b0, elemwiseAdd a1 b1].getD r
        (zeroTensor [lDim, d])).shape = [lDim, d] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hsum0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hsum1
  have hshapeA : (allGatherPrimDimN 0 2 0 [a0, a1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadA]
    simp only [List.set, List.getD_cons_zero]
  have hshapeB : (allGatherPrimDimN 0 2 0 [b0, b1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadB]
    simp only [List.set, List.getD_cons_zero]
  have hshapeS : (allGatherPrimDimN 0 2 0
      [elemwiseAdd a0 b0, elemwiseAdd a1 b1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadS]
    simp only [List.set, List.getD_cons_zero]
  have hlhsShape : (elemwiseAdd (allGatherPrimDimN 0 2 0 [a0, a1])
      (allGatherPrimDimN 0 2 0 [b0, b1])).shape = [lDim * 2, d] :=
    elemwiseAdd_shape_of_shapes _ _ [lDim * 2, d] hshapeA hshapeB
  refine Tensor.ext ?_ ?_
  · rw [hlhsShape, hshapeS]
  · intro idx hidx
    rw [hlhsShape, prodShape_2d] at hidx
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
    rw [elemwiseAdd_valAt_2d _ _ (lDim * 2) d idx hshapeA hshapeB hd hidx]
    rw [hflat]
    rw [allGatherPrimDimN0_valAt 2 lDim d [a0, a1] (by decide) hl hd
      hheadA hgetA r hr i hi j hj]
    rw [allGatherPrimDimN0_valAt 2 lDim d [b0, b1] (by decide) hl hd
      hheadB hgetB r hr i hi j hj]
    rw [allGatherPrimDimN0_valAt 2 lDim d [elemwiseAdd a0 b0, elemwiseAdd a1 b1]
      (by decide) hl hd hheadS hgetS r hr i hi j hj]
    interval_cases r
    · simp only [List.getD_cons_zero]
      exact (elemwiseAdd_valAt_2d a0 b0 lDim d _ ha0 hb0 hd hloc).symm
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact (elemwiseAdd_valAt_2d a1 b1 lDim d _ ha1 hb1 hd hloc).symm

/-! ## `elemwiseAdd` commutes with the faithful CP2 shuffle -/

/-- The faithful CP2 shuffle only relocates whole flat slots (`gatherFromRank`),
so a pointwise binary operator distributes over it on every rank. -/
theorem elemwiseAdd_shuffle_collective_cp2
    (a0 a1 b0 b1 : Tensor) (cu : List Nat) (lDim d rank : Nat)
    (hl : 0 < lDim) (hd : 0 < d) (hrank : rank < 2)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d])
    (hb0 : b0.shape = [lDim, d]) (hb1 : b1.shape = [lDim, d]) :
    elemwiseAdd (fw_maybe_shuffle_collective [a0, a1] cu 2 rank)
        (fw_maybe_shuffle_collective [b0, b1] cu 2 rank) =
      fw_maybe_shuffle_collective
        [elemwiseAdd a0 b0, elemwiseAdd a1 b1] cu 2 rank := by
  have hsum0 : (elemwiseAdd a0 b0).shape = [lDim, d] :=
    elemwiseAdd_shape_of_shapes a0 b0 [lDim, d] ha0 hb0
  have hsum1 : (elemwiseAdd a1 b1).shape = [lDim, d] :=
    elemwiseAdd_shape_of_shapes a1 b1 [lDim, d] ha1 hb1
  have hlocA : ([a0, a1].getD rank (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using ha0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using ha1
  have hlocB : ([b0, b1].getD rank (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hb0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hb1
  have hlocS : ([elemwiseAdd a0 b0, elemwiseAdd a1 b1].getD rank
      (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hsum0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hsum1
  have hshA : (fw_maybe_shuffle_collective [a0, a1] cu 2 rank).shape =
      [lDim, d] := by rw [fw_maybe_shuffle_collective_shape, hlocA]
  have hshB : (fw_maybe_shuffle_collective [b0, b1] cu 2 rank).shape =
      [lDim, d] := by rw [fw_maybe_shuffle_collective_shape, hlocB]
  have hshS : (fw_maybe_shuffle_collective
      [elemwiseAdd a0 b0, elemwiseAdd a1 b1] cu 2 rank).shape = [lDim, d] := by
    rw [fw_maybe_shuffle_collective_shape, hlocS]
  have hlhsShape : (elemwiseAdd (fw_maybe_shuffle_collective [a0, a1] cu 2 rank)
      (fw_maybe_shuffle_collective [b0, b1] cu 2 rank)).shape = [lDim, d] :=
    elemwiseAdd_shape_of_shapes _ _ [lDim, d] hshA hshB
  refine Tensor.ext ?_ ?_
  · rw [hlhsShape, hshS]
  · intro idx hidx
    rw [hlhsShape, prodShape_2d] at hidx
    rw [elemwiseAdd_valAt_2d _ _ lDim d idx hshA hshB hd hidx]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocA, prodShape_2d]; exact hidx)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocB, prodShape_2d]; exact hidx)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocS, prodShape_2d]; exact hidx)]
    simp only [hlocA, hlocB, hlocS, List.tail_cons, prodShape, List.foldl,
      Nat.one_mul, List.getD_cons_zero]
    unfold gatherFromRank
    set g := zigzagPos cu 2 rank (idx / d) with hg
    set off := g % lDim * d + idx % d with hoff
    have hoffLt : off < lDim * d := by
      have h1 : g % lDim < lDim := Nat.mod_lt _ hl
      have h2 : idx % d < d := Nat.mod_lt _ hd
      calc off < g % lDim * d + d := by omega
        _ = (g % lDim + 1) * d := by ring
        _ ≤ lDim * d := Nat.mul_le_mul_right _ h1
    by_cases h0 : g / lDim = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact (elemwiseAdd_valAt_2d a0 b0 lDim d off ha0 hb0 hd hoffLt).symm
    · by_cases h1 : g / lDim = 1
      · rw [h1]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        exact (elemwiseAdd_valAt_2d a1 b1 lDim d off ha1 hb1 hd hoffLt).symm
      · have hge : ∀ n : Nat, ¬ n = 0 → ¬ n = 1 → 2 ≤ n := by intro n u v; omega
        have hnot : 2 ≤ g / lDim := hge _ h0 h1
        have hgA : [a0, a1].getD (g / lDim) (zeroTensor []) = zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        have hgB : [b0, b1].getD (g / lDim) (zeroTensor []) = zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        have hgS : [elemwiseAdd a0 b0, elemwiseAdd a1 b1].getD (g / lDim)
            (zeroTensor []) = zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        simp only [hgA, hgB, hgS, valAt_zeroTensor_empty, add_zero]

/-! ## Metadata well-formedness transports along a pointwise binary operator -/

/-- Elementwise addition of two same-shaped CP2 source shard pairs preserves
packed-sequence well-formedness: the contract only mentions metadata and the
dim-0 token count, both of which are unchanged. -/
theorem ZigzagCuWF.elemwiseAdd_cp2
    (cu : List Nat) (a0 a1 b0 b1 : Tensor) (lDim d : Nat)
    (hwf : ZigzagCuWF cu [a0, a1] 2)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d])
    (hb0 : b0.shape = [lDim, d]) (hb1 : b1.shape = [lDim, d]) :
    ZigzagCuWF cu [elemwiseAdd a0 b0, elemwiseAdd a1 b1] 2 := by
  have hsum0 : (elemwiseAdd a0 b0).shape = [lDim, d] :=
    elemwiseAdd_shape_of_shapes a0 b0 [lDim, d] ha0 hb0
  have hsum1 : (elemwiseAdd a1 b1).shape = [lDim, d] :=
    elemwiseAdd_shape_of_shapes a1 b1 [lDim, d] ha1 hb1
  refine ⟨hwf.cp_pos, rfl, hwf.cu_starts_zero, hwf.cu_has_endpoint,
    hwf.monotone, hwf.divisible, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hsum0]; exact List.cons_ne_nil _ _
    · rw [hsum1]; exact List.cons_ne_nil _ _
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rfl
    · simp only [List.getD_cons_zero, hsum0, hsum1]
  · have h := hwf.local_tokens
    simp only [List.getD_cons_zero, ha0] at h
    simpa only [List.getD_cons_zero, hsum0] using h

namespace Zigzag2Rel

/-! ## (1) Identity `fw_view` -/

/-- A `fw_view` whose target shape equals the operand's own shape is the
identity, hence trivially preserves the CP2 zigzag layout relation.  This is the
graph's SM node 506 `FW_reshape [4096, 1024]` applied to tensor 5348, which
already has shape `[4096, 1024]` (per-rank: `[2048, 1024]`). -/
theorem view_id
    {full z0 z1 cu : Tensor} (lDim d : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, d] [lDim, d]) :
    Zigzag2Rel
      (fw_view [lDim * 2, d] full)
      (fw_view [lDim, d] z0)
      (fw_view [lDim, d] z1)
      cu [lDim * 2, d] [lDim, d] := by
  rw [fw_view_id full [lDim * 2, d] hrel.full_shape,
    fw_view_id z0 [lDim, d] hrel.rank0_shape,
    fw_view_id z1 [lDim, d] hrel.rank1_shape]
  exact hrel

/-- Shape-agnostic version of `view_id`. -/
theorem view_id'
    {full z0 z1 cu : Tensor} {fullShape shardShape : Shape}
    (hrel : Zigzag2Rel full z0 z1 cu fullShape shardShape) :
    Zigzag2Rel
      (fw_view fullShape full)
      (fw_view shardShape z0)
      (fw_view shardShape z1)
      cu fullShape shardShape := by
  rw [fw_view_id full fullShape hrel.full_shape,
    fw_view_id z0 shardShape hrel.rank0_shape,
    fw_view_id z1 shardShape hrel.rank1_shape]
  exact hrel

/-! ## (2) `FW_float`

The core library has **no separate tensor-level `fw_float` function**: the cast
is modelled as the identity directly at the `evalOp` layer, via
`evalOp_fw_float : evalOp _ _ "OpName.FW_float" params [x] = [x]`.  The
propagation lemma is therefore stated in exactly the shape the graph bridge
consumes (`(evalOp …).headD (zeroTensor [])`). -/

theorem fw_float
    {full z0 z1 cu : Tensor} {fullShape shardShape : Shape}
    (numParts rankF rank0 rank1 : Nat) (params : List Nat)
    (hrel : Zigzag2Rel full z0 z1 cu fullShape shardShape) :
    Zigzag2Rel
      ((evalOp numParts rankF "OpName.FW_float" params [full]).headD (zeroTensor []))
      ((evalOp numParts rank0 "OpName.FW_float" params [z0]).headD (zeroTensor []))
      ((evalOp numParts rank1 "OpName.FW_float" params [z1]).headD (zeroTensor []))
      cu fullShape shardShape := by
  rw [evalOp_fw_float, evalOp_fw_float, evalOp_fw_float]
  exact hrel

/-! ## (3) Elementwise `FW_add` (residual connection)

`OpName.FW_add` denotes `elemwiseAdd` (`evalOp_fw_add2`); there is no `fw_add`
identifier in the core library, so the statement uses `elemwiseAdd`. -/

/-- Two CP2 zigzag tensors sharing the **same** `cu` metadata can be added
elementwise, and the sum is again in CP2 zigzag layout with that same `cu`.
This is the residual connection: SM node 510 `FW_add ins [8143, 5353]`,
PM nodes 1078/1079. -/
theorem add
    {fullA zA0 zA1 fullB zB0 zB1 cu : Tensor} (lDim d : Nat)
    (hA : Zigzag2Rel fullA zA0 zA1 cu [lDim * 2, d] [lDim, d])
    (hB : Zigzag2Rel fullB zB0 zB1 cu [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    Zigzag2Rel (elemwiseAdd fullA fullB) (elemwiseAdd zA0 zB0)
      (elemwiseAdd zA1 zB1) cu [lDim * 2, d] [lDim, d] := by
  rcases hA with ⟨a0, a1, hAs⟩
  rcases hB with ⟨b0, b1, hBs⟩
  have ha0 : a0.shape = [lDim, d] := hAs.source0_shape
  have ha1 : a1.shape = [lDim, d] := hAs.source1_shape
  have hb0 : b0.shape = [lDim, d] := hBs.source0_shape
  have hb1 : b1.shape = [lDim, d] := hBs.source1_shape
  refine ⟨elemwiseAdd a0 b0, elemwiseAdd a1 b1, ?_, ?_, ?_, ?_,
    elemwiseAdd_shape_of_shapes a0 b0 [lDim, d] ha0 hb0,
    elemwiseAdd_shape_of_shapes a1 b1 [lDim, d] ha1 hb1, ?_, ?_,
    ZigzagCuWF.elemwiseAdd_cp2 (decodeCuSeqlens cu) a0 a1 b0 b1 lDim d
      hAs.cu_wf ha0 ha1 hb0 hb1⟩
  · rw [hAs.full_value, hBs.full_value]
    exact elemwiseAdd_allGather0_commute_cp2 a0 a1 b0 b1 lDim d hl hd
      ha0 ha1 hb0 hb1
  · rw [hAs.rank0_value, hBs.rank0_value]
    exact elemwiseAdd_shuffle_collective_cp2 a0 a1 b0 b1 (decodeCuSeqlens cu)
      lDim d 0 hl hd (by decide) ha0 ha1 hb0 hb1
  · rw [hAs.rank1_value, hBs.rank1_value]
    exact elemwiseAdd_shuffle_collective_cp2 a0 a1 b0 b1 (decodeCuSeqlens cu)
      lDim d 1 hl hd (by decide) ha0 ha1 hb0 hb1
  · exact elemwiseAdd_shape_of_shapes fullA fullB [lDim * 2, d]
      hAs.full_shape hBs.full_shape
  · exact elemwiseAdd_shape_of_shapes zA0 zB0 [lDim, d]
      hAs.rank0_shape hBs.rank0_shape
  · exact elemwiseAdd_shape_of_shapes zA1 zB1 [lDim, d]
      hAs.rank1_shape hBs.rank1_shape

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
