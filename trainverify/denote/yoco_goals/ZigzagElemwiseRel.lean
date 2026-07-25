/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagPointwiseRel

/-!
# Elementwise operators preserve the CP2 zigzag layout relation

Three propagation lemmas for `Zigzag2Rel`, covering the elementwise activation
operators of the YOCO/MoE graph:

* `Zigzag2Rel.sigmoid` — `OpName.FW_sigmoid`, denoted by `fw_sigmoid`
  (`denote/Denote.lean`), a *unary* elementwise map.
* `Zigzag2Rel.swiglu` — `OpName.FW_swiglu`, denoted by `fw_swiglu gate up`,
  a *binary* elementwise map (`silu(gate) ⊙ up`), the two operands sharing the
  same `cu` metadata.
* `Zigzag2Rel.mul` — `OpName.FW_mul`.  The core library dispatches this to
  `elemwiseMul` (see `evalOp_fw_mul2`); there is **no** `fw_mul` identifier, so
  the statement below is phrased with `elemwiseMul`.

All three are row-local (indeed slot-local), hence they commute both with the
ordinary dim-0 all-gather (a flat concatenation) and with the faithful zigzag
shuffle (which relocates whole flat slots via `gatherFromRank`).

The core library carries no shape-generic all-gather / shuffle commutation
lemmas for these operators, so we prove them here.  To avoid triplicating the
same argument, the two commutations are proved **once** in a generic form,
parameterised over an arbitrary tensor-level unary (resp. binary) operator
together with its shape and pointwise-value contract; the three concrete
operators are then discharged by supplying those contracts.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

namespace ZigzagElemwise

/-! ## Small arithmetic / indexing helpers -/

theorem prodShape_2d' (a b : Nat) : prodShape [a, b] = a * b := by
  simp only [prodShape, List.foldl, Nat.one_mul]

/-- `omega` cannot go from `¬ n = 0 ∧ ¬ n = 1` to `2 ≤ n` inside a `by_cases`
chain without help; this is the explicit helper. -/
theorem two_le_of_ne_zero_ne_one : ∀ n : Nat, ¬ n = 0 → ¬ n = 1 → 2 ≤ n := by
  intro n u v; omega

/-! ## A range bound for `zigzagPos`

For the *binary* operators below the out-of-range shuffle branch is harmless
(`f 0 0 = 0`), exactly as in `ZigzagPointwiseRel`.  For `fw_sigmoid` it is not:
`sigmoidScalar 0 = 1/2 ≠ 0`.  We therefore prove that under `ZigzagCuWF` the
branch is *unreachable*: `zigzagPos` always lands inside the packed sequence. -/

/-- Every entry of a monotone cumulative-sequence list is bounded by its last
entry. -/
theorem getD_le_getD_last (cu : List Nat)
    (hmono : ∀ s, s + 1 < cu.length → cu.getD s 0 ≤ cu.getD (s + 1) 0) :
    ∀ n j, j + n = cu.length - 1 → j < cu.length →
      cu.getD j 0 ≤ cu.getD (cu.length - 1) 0 := by
  intro n
  induction n with
  | zero =>
    intro j hj _
    rw [Nat.add_zero] at hj
    rw [hj]
  | succ n ih =>
    intro j hj hjlt
    have hnext : j + 1 < cu.length := by omega
    exact le_trans (hmono j hnext) (ih (j + 1) (by omega) hnext)

theorem listLast!_eq_getD (cu : List Nat) :
    listLast! cu = cu.getD (cu.length - 1) 0 := by
  unfold listLast!
  rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- Out-of-range `getD` on a `List Nat` is the default. -/
theorem getD_of_ge (cu : List Nat) (j : Nat) (h : cu.length ≤ j) :
    cu.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

/-- The zigzag walker never leaves the packed sequence. -/
theorem zigzagPosAux_lt (cu : List Nat) (ts cpRank L : Nat)
    (hts : 0 < ts) (hrank : cpRank < ts) (hL : 0 < L)
    (hmono : ∀ s, s + 1 < cu.length → cu.getD s 0 ≤ cu.getD (s + 1) 0)
    (hdiv : ∀ s, s + 1 < cu.length → (cu.getD (s + 1) 0 - cu.getD s 0) % ts = 0)
    (hlast : ∀ s, s + 1 < cu.length → cu.getD (s + 1) 0 ≤ L) :
    ∀ fuel k s, zigzagPosAux cu ts cpRank k s fuel < L := by
  intro fuel
  induction fuel with
  | zero => intro k s; exact hL
  | succ fuel ih =>
    intro k s
    show (let sl := sliceSizeAt cu ts s
          let seqStart := cu.getD s 0
          if k < sl then seqStart + cpRank * sl + k
          else if k < 2 * sl then
            seqStart + (ts - cpRank - 1) * sl + (k - sl)
          else zigzagPosAux cu ts cpRank (k - 2 * sl) (s + 1) fuel) < L
    dsimp only []
    set sl := sliceSizeAt cu ts s with hsl
    -- `sl > 0` forces the segment to exist and to be exactly `sl * ts` long.
    have hseg : 0 < sl → s + 1 < cu.length ∧
        sl * ts = cu.getD (s + 1) 0 - cu.getD s 0 := by
      intro hpos
      have hlen : s + 1 < cu.length := by
        by_contra hc
        have h0 : cu.getD (s + 1) 0 = 0 := getD_of_ge cu (s + 1) (by omega)
        have : sl = 0 := by
          rw [hsl]
          show (cu.getD (s + 1) 0 - cu.getD s 0) / ts = 0
          rw [h0, Nat.zero_sub, Nat.zero_div]
        omega
      refine ⟨hlen, ?_⟩
      have hd := hdiv s hlen
      have : sl = (cu.getD (s + 1) 0 - cu.getD s 0) / ts := rfl
      rw [this]
      exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)
    by_cases h1 : k < sl
    · rw [if_pos h1]
      obtain ⟨hlen, heq⟩ := hseg (by omega)
      have hm := hmono s hlen
      have hlst := hlast s hlen
      have he1 : (cpRank + 1) * sl = cpRank * sl + sl := by ring
      have he2 : (cpRank + 1) * sl ≤ ts * sl :=
        Nat.mul_le_mul_right sl (by omega)
      have he3 : ts * sl = sl * ts := Nat.mul_comm _ _
      omega
    · rw [if_neg h1]
      by_cases h2 : k < 2 * sl
      · rw [if_pos h2]
        have hpos : 0 < sl := by omega
        obtain ⟨hlen, heq⟩ := hseg hpos
        have hm := hmono s hlen
        have hlst := hlast s hlen
        have he1 : (ts - cpRank - 1 + 1) * sl = (ts - cpRank - 1) * sl + sl := by
          ring
        have he2 : (ts - cpRank - 1 + 1) * sl ≤ ts * sl :=
          Nat.mul_le_mul_right sl (by omega)
        have he3 : ts * sl = sl * ts := Nat.mul_comm _ _
        omega
      · rw [if_neg h2]
        exact ih _ _

/-- Under `ZigzagCuWF` with `cpSize = 2` and shard row count `lDim`, the zigzag
source position of any local token lies in `[0, 2 * lDim)`. -/
theorem zigzagPos_lt_of_wf (cu : List Nat) (a0 a1 : Tensor) (lDim d : Nat)
    (hwf : ZigzagCuWF cu [a0, a1] 2) (ha0 : a0.shape = [lDim, d])
    (hl : 0 < lDim) (rank : Nat) (hrank : rank < 2) (token : Nat) :
    zigzagPos cu 2 rank token < lDim * 2 := by
  have hlocal := hwf.local_tokens
  simp only [List.getD_cons_zero, ha0, List.getD_cons_zero] at hlocal
  have hLast : lDim * 2 = listLast! cu := hlocal
  have hLpos : 0 < lDim * 2 := by omega
  have hlastLe : ∀ s, s + 1 < cu.length → cu.getD (s + 1) 0 ≤ lDim * 2 := by
    intro s hs
    rw [hLast, listLast!_eq_getD]
    exact getD_le_getD_last cu hwf.monotone (cu.length - 1 - (s + 1)) (s + 1)
      (by omega) hs
  show zigzagPosAux cu (2 * 2) rank token 0 (cu.length - 1) < lDim * 2
  exact zigzagPosAux_lt cu (2 * 2) rank (lDim * 2) (by omega) (by omega) hLpos
    hwf.monotone hwf.divisible hlastLe _ _ _

/-! ## Generic unary elementwise operator

`u` is any tensor map that preserves the shape and acts slotwise by a scalar
function `f` with `f 0 = 0`. -/

section Unary

variable (u : Tensor → Tensor) (f : Scalar → Scalar)

/-- Pointwise unary maps distribute over the ordinary CP2 dim-0 all-gather. -/
theorem unary_allGather0_commute_cp2
    (hshape : ∀ x : Tensor, (u x).shape = x.shape)
    (hval : ∀ (x : Tensor) (idx : Nat), idx < prodShape x.shape →
      valAt (u x) idx = f (valAt x idx))
    (a0 a1 : Tensor) (lDim d : Nat)
    (hl : 0 < lDim) (hd : 0 < d)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d]) :
    u (allGatherPrimDimN 0 2 0 [a0, a1]) =
      allGatherPrimDimN 0 2 0 [u a0, u a1] := by
  have hu0 : (u a0).shape = [lDim, d] := by rw [hshape, ha0]
  have hu1 : (u a1).shape = [lDim, d] := by rw [hshape, ha1]
  have hheadA : (([a0, a1].head?.map (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, ha0]
  have hheadU : (([u a0, u a1].head?.map (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hu0]
  have hgetA : ∀ r (_ : r < 2),
      ([a0, a1].getD r (zeroTensor [lDim, d])).shape = [lDim, d] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using ha0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using ha1
  have hgetU : ∀ r (_ : r < 2),
      ([u a0, u a1].getD r (zeroTensor [lDim, d])).shape = [lDim, d] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hu0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hu1
  have hshapeA : (allGatherPrimDimN 0 2 0 [a0, a1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadA]
    simp only [List.set, List.getD_cons_zero]
  have hshapeU : (allGatherPrimDimN 0 2 0 [u a0, u a1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadU]
    simp only [List.set, List.getD_cons_zero]
  have hlhsShape : (u (allGatherPrimDimN 0 2 0 [a0, a1])).shape = [lDim * 2, d] := by
    rw [hshape, hshapeA]
  refine Tensor.ext ?_ ?_
  · rw [hlhsShape, hshapeU]
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
    rw [hval _ idx (by rw [hshapeA, prodShape_2d']; exact hidx)]
    rw [hflat]
    rw [allGatherPrimDimN0_valAt 2 lDim d [a0, a1] (by decide) hl hd
      hheadA hgetA r hr i hi j hj]
    rw [allGatherPrimDimN0_valAt 2 lDim d [u a0, u a1] (by decide) hl hd
      hheadU hgetU r hr i hi j hj]
    interval_cases r
    · simp only [List.getD_cons_zero]
      exact (hval a0 _ (by rw [ha0, prodShape_2d']; exact hloc)).symm
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact (hval a1 _ (by rw [ha1, prodShape_2d']; exact hloc)).symm

/-- Pointwise unary maps distribute over the faithful CP2 shuffle. -/
theorem unary_shuffle_collective_cp2
    (hshape : ∀ x : Tensor, (u x).shape = x.shape)
    (hval : ∀ (x : Tensor) (idx : Nat), idx < prodShape x.shape →
      valAt (u x) idx = f (valAt x idx))
    (a0 a1 : Tensor) (cu : List Nat) (lDim d rank : Nat)
    (hl : 0 < lDim) (hd : 0 < d) (hrank : rank < 2)
    (hwf : ZigzagCuWF cu [a0, a1] 2)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d]) :
    u (fw_maybe_shuffle_collective [a0, a1] cu 2 rank) =
      fw_maybe_shuffle_collective [u a0, u a1] cu 2 rank := by
  have hu0 : (u a0).shape = [lDim, d] := by rw [hshape, ha0]
  have hu1 : (u a1).shape = [lDim, d] := by rw [hshape, ha1]
  have hlocA : ([a0, a1].getD rank (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using ha0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using ha1
  have hlocU : ([u a0, u a1].getD rank (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hu0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hu1
  have hshA : (fw_maybe_shuffle_collective [a0, a1] cu 2 rank).shape =
      [lDim, d] := by rw [fw_maybe_shuffle_collective_shape, hlocA]
  have hshU : (fw_maybe_shuffle_collective [u a0, u a1] cu 2 rank).shape =
      [lDim, d] := by rw [fw_maybe_shuffle_collective_shape, hlocU]
  have hlhsShape : (u (fw_maybe_shuffle_collective [a0, a1] cu 2 rank)).shape =
      [lDim, d] := by rw [hshape, hshA]
  refine Tensor.ext ?_ ?_
  · rw [hlhsShape, hshU]
  · intro idx hidx
    rw [hlhsShape, prodShape_2d'] at hidx
    rw [hval _ idx (by rw [hshA, prodShape_2d']; exact hidx)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocA, prodShape_2d']; exact hidx)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocU, prodShape_2d']; exact hidx)]
    simp only [hlocA, hlocU, List.tail_cons, prodShape, List.foldl,
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
      exact (hval a0 off (by rw [ha0, prodShape_2d']; exact hoffLt)).symm
    · by_cases h1 : g / lDim = 1
      · rw [h1]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        exact (hval a1 off (by rw [ha1, prodShape_2d']; exact hoffLt)).symm
      · have hnot : 2 ≤ g / lDim := two_le_of_ne_zero_ne_one _ h0 h1
        exfalso
        have hglt : g < lDim * 2 :=
          zigzagPos_lt_of_wf cu a0 a1 lDim d hwf ha0 hl rank hrank (idx / d)
        have : g / lDim < 2 := (Nat.div_lt_iff_lt_mul hl).mpr
          (by rw [Nat.mul_comm]; exact hglt)
        omega

/-- Metadata well-formedness transports along a shape-preserving unary map. -/
theorem ZigzagCuWF_unary_cp2
    (hshape : ∀ x : Tensor, (u x).shape = x.shape)
    (cu : List Nat) (a0 a1 : Tensor) (lDim d : Nat)
    (hwf : ZigzagCuWF cu [a0, a1] 2)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d]) :
    ZigzagCuWF cu [u a0, u a1] 2 := by
  have hu0 : (u a0).shape = [lDim, d] := by rw [hshape, ha0]
  have hu1 : (u a1).shape = [lDim, d] := by rw [hshape, ha1]
  refine ⟨hwf.cp_pos, rfl, hwf.cu_starts_zero, hwf.cu_has_endpoint,
    hwf.monotone, hwf.divisible, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hu0]; exact List.cons_ne_nil _ _
    · rw [hu1]; exact List.cons_ne_nil _ _
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rfl
    · simp only [List.getD_cons_zero, hu0, hu1]
  · have h := hwf.local_tokens
    simp only [List.getD_cons_zero, ha0] at h
    simpa only [List.getD_cons_zero, hu0] using h

end Unary

/-! ## Generic binary elementwise operator -/

section Binary

variable (op : Tensor → Tensor → Tensor) (f : Scalar → Scalar → Scalar)

/-- Pointwise binary maps distribute over the ordinary CP2 dim-0 all-gather. -/
theorem binary_allGather0_commute_cp2
    (hshape : ∀ (x y : Tensor) (sh : Shape), x.shape = sh → y.shape = sh →
      (op x y).shape = sh)
    (hval : ∀ (x y : Tensor) (a b idx : Nat), x.shape = [a, b] → y.shape = [a, b] →
      idx < a * b → valAt (op x y) idx = f (valAt x idx) (valAt y idx))
    (a0 a1 b0 b1 : Tensor) (lDim d : Nat)
    (hl : 0 < lDim) (hd : 0 < d)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d])
    (hb0 : b0.shape = [lDim, d]) (hb1 : b1.shape = [lDim, d]) :
    op (allGatherPrimDimN 0 2 0 [a0, a1]) (allGatherPrimDimN 0 2 0 [b0, b1]) =
      allGatherPrimDimN 0 2 0 [op a0 b0, op a1 b1] := by
  have hheadA : (([a0, a1].head?.map (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, ha0]
  have hheadB : (([b0, b1].head?.map (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hb0]
  have hs0 : (op a0 b0).shape = [lDim, d] := hshape a0 b0 [lDim, d] ha0 hb0
  have hs1 : (op a1 b1).shape = [lDim, d] := hshape a1 b1 [lDim, d] ha1 hb1
  have hheadS : (([op a0 b0, op a1 b1].head?.map
      (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hs0]
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
      ([op a0 b0, op a1 b1].getD r (zeroTensor [lDim, d])).shape = [lDim, d] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hs0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
  have hshapeA : (allGatherPrimDimN 0 2 0 [a0, a1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadA]
    simp only [List.set, List.getD_cons_zero]
  have hshapeB : (allGatherPrimDimN 0 2 0 [b0, b1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadB]
    simp only [List.set, List.getD_cons_zero]
  have hshapeS : (allGatherPrimDimN 0 2 0 [op a0 b0, op a1 b1]).shape =
      [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadS]
    simp only [List.set, List.getD_cons_zero]
  have hlhsShape : (op (allGatherPrimDimN 0 2 0 [a0, a1])
      (allGatherPrimDimN 0 2 0 [b0, b1])).shape = [lDim * 2, d] :=
    hshape _ _ [lDim * 2, d] hshapeA hshapeB
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
    rw [hval _ _ (lDim * 2) d idx hshapeA hshapeB hidx]
    rw [hflat]
    rw [allGatherPrimDimN0_valAt 2 lDim d [a0, a1] (by decide) hl hd
      hheadA hgetA r hr i hi j hj]
    rw [allGatherPrimDimN0_valAt 2 lDim d [b0, b1] (by decide) hl hd
      hheadB hgetB r hr i hi j hj]
    rw [allGatherPrimDimN0_valAt 2 lDim d [op a0 b0, op a1 b1]
      (by decide) hl hd hheadS hgetS r hr i hi j hj]
    interval_cases r
    · simp only [List.getD_cons_zero]
      exact (hval a0 b0 lDim d _ ha0 hb0 hloc).symm
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact (hval a1 b1 lDim d _ ha1 hb1 hloc).symm

/-- Pointwise binary maps distribute over the faithful CP2 shuffle. -/
theorem binary_shuffle_collective_cp2
    (hshape : ∀ (x y : Tensor) (sh : Shape), x.shape = sh → y.shape = sh →
      (op x y).shape = sh)
    (hval : ∀ (x y : Tensor) (a b idx : Nat), x.shape = [a, b] → y.shape = [a, b] →
      idx < a * b → valAt (op x y) idx = f (valAt x idx) (valAt y idx))
    (hzero : f 0 0 = 0)
    (a0 a1 b0 b1 : Tensor) (cu : List Nat) (lDim d rank : Nat)
    (hl : 0 < lDim) (hd : 0 < d) (hrank : rank < 2)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d])
    (hb0 : b0.shape = [lDim, d]) (hb1 : b1.shape = [lDim, d]) :
    op (fw_maybe_shuffle_collective [a0, a1] cu 2 rank)
        (fw_maybe_shuffle_collective [b0, b1] cu 2 rank) =
      fw_maybe_shuffle_collective [op a0 b0, op a1 b1] cu 2 rank := by
  have hs0 : (op a0 b0).shape = [lDim, d] := hshape a0 b0 [lDim, d] ha0 hb0
  have hs1 : (op a1 b1).shape = [lDim, d] := hshape a1 b1 [lDim, d] ha1 hb1
  have hlocA : ([a0, a1].getD rank (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using ha0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using ha1
  have hlocB : ([b0, b1].getD rank (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hb0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hb1
  have hlocS : ([op a0 b0, op a1 b1].getD rank (zeroTensor [])).shape =
      [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hs0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
  have hshA : (fw_maybe_shuffle_collective [a0, a1] cu 2 rank).shape =
      [lDim, d] := by rw [fw_maybe_shuffle_collective_shape, hlocA]
  have hshB : (fw_maybe_shuffle_collective [b0, b1] cu 2 rank).shape =
      [lDim, d] := by rw [fw_maybe_shuffle_collective_shape, hlocB]
  have hshS : (fw_maybe_shuffle_collective [op a0 b0, op a1 b1] cu 2 rank).shape =
      [lDim, d] := by rw [fw_maybe_shuffle_collective_shape, hlocS]
  have hlhsShape : (op (fw_maybe_shuffle_collective [a0, a1] cu 2 rank)
      (fw_maybe_shuffle_collective [b0, b1] cu 2 rank)).shape = [lDim, d] :=
    hshape _ _ [lDim, d] hshA hshB
  refine Tensor.ext ?_ ?_
  · rw [hlhsShape, hshS]
  · intro idx hidx
    rw [hlhsShape, prodShape_2d'] at hidx
    rw [hval _ _ lDim d idx hshA hshB hidx]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocA, prodShape_2d']; exact hidx)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocB, prodShape_2d']; exact hidx)]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocS, prodShape_2d']; exact hidx)]
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
      exact (hval a0 b0 lDim d off ha0 hb0 hoffLt).symm
    · by_cases h1 : g / lDim = 1
      · rw [h1]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        exact (hval a1 b1 lDim d off ha1 hb1 hoffLt).symm
      · have hnot : 2 ≤ g / lDim := two_le_of_ne_zero_ne_one _ h0 h1
        have hgA : [a0, a1].getD (g / lDim) (zeroTensor []) = zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        have hgB : [b0, b1].getD (g / lDim) (zeroTensor []) = zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        have hgS : [op a0 b0, op a1 b1].getD (g / lDim) (zeroTensor []) =
            zeroTensor [] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simpa using hnot), Option.getD_none]
        simp only [hgA, hgB, hgS, valAt_zeroTensor_empty, hzero]

/-- Metadata well-formedness transports along a shape-preserving binary map. -/
theorem ZigzagCuWF_binary_cp2
    (hshape : ∀ (x y : Tensor) (sh : Shape), x.shape = sh → y.shape = sh →
      (op x y).shape = sh)
    (cu : List Nat) (a0 a1 b0 b1 : Tensor) (lDim d : Nat)
    (hwf : ZigzagCuWF cu [a0, a1] 2)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d])
    (hb0 : b0.shape = [lDim, d]) (hb1 : b1.shape = [lDim, d]) :
    ZigzagCuWF cu [op a0 b0, op a1 b1] 2 := by
  have hs0 : (op a0 b0).shape = [lDim, d] := hshape a0 b0 [lDim, d] ha0 hb0
  have hs1 : (op a1 b1).shape = [lDim, d] := hshape a1 b1 [lDim, d] ha1 hb1
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

end Binary

/-! ## Contracts for the three concrete operators -/

/-! ### `fw_sigmoid` -/

theorem fw_sigmoid_shape (x : Tensor) : (fw_sigmoid x).shape = x.shape := rfl

theorem fw_sigmoid_valAt (x : Tensor) (idx : Nat) (h : idx < prodShape x.shape) :
    valAt (fw_sigmoid x) idx = sigmoidScalar (valAt x idx) := by
  unfold fw_sigmoid
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using h)]
  rfl

theorem sigmoidScalar_zero_mul_zero : sigmoidScalar 0 * 0 = 0 := by
  rw [mul_zero]

/-! ### `fw_swiglu` -/

theorem fw_swiglu_shape_of_shapes (gate up : Tensor) (sh : Shape)
    (_hg : gate.shape = sh) (hu : up.shape = sh) :
    (fw_swiglu gate up).shape = sh := by
  unfold fw_swiglu Tensor.mkShape
  exact hu

theorem fw_swiglu_valAt (gate up : Tensor) (idx : Nat)
    (h : idx < prodShape up.shape) :
    valAt (fw_swiglu gate up) idx =
      siluScalar (valAt gate idx) * valAt up idx := by
  unfold fw_swiglu
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using h)]
  rfl

/-! ### `elemwiseMul` (the denotation of `OpName.FW_mul`) -/

theorem elemwiseMul_shape_of_shapes' (x y : Tensor) (sh : Shape)
    (hx : x.shape = sh) (hy : y.shape = sh) :
    (elemwiseMul x y).shape = sh := by
  unfold elemwiseMul Tensor.mkShape
  change outShape2 x y = sh
  simp [outShape2, hx, hy]

/-- Same-shape 2D elementwise multiply is pointwise on flat indices.  (Mirrors
`ZigzagPointwiseRel.elemwiseAdd_valAt_2d`, which handles the broadcast layer.) -/
theorem elemwiseMul_valAt_2d (x y : Tensor) (a b idx : Nat)
    (hx : x.shape = [a, b]) (hy : y.shape = [a, b]) (hb : 0 < b)
    (hidx : idx < a * b) :
    valAt (elemwiseMul x y) idx = valAt x idx * valAt y idx := by
  have hout : (elemwiseMul x y).shape = [a, b] :=
    elemwiseMul_shape_of_shapes' x y [a, b] hx hy
  have hos : outShape2 x y = [a, b] := by
    simp only [outShape2, hx, hy, List.length_cons, List.length_nil,
      Nat.max_self, Nat.sub_self, List.replicate, List.nil_append,
      List.zipWith, Nat.max_self]
  have hstep : valAt (elemwiseMul x y) idx =
      broadcastValAtShape (outShape2 x y) x idx *
        broadcastValAtShape (outShape2 x y) y idx := by
    rw [valAt_of_lt _ _ (by rw [hout, prodShape_2d']; exact hidx)]
    rfl
  rw [hstep, hos, broadcastValAtShape_self_2d x a b idx hx hb hidx,
    broadcastValAtShape_self_2d y a b idx hy hb hidx]

end ZigzagElemwise

open ZigzagElemwise

namespace Zigzag2Rel

/-! ## (1) `fw_sigmoid` (`OpName.FW_sigmoid`) -/

/-- The unary elementwise sigmoid preserves the CP2 zigzag layout relation;
shapes are unchanged. -/
theorem sigmoid
    {full z0 z1 cu : Tensor} (lDim d : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    Zigzag2Rel (fw_sigmoid full) (fw_sigmoid z0) (fw_sigmoid z1)
      cu [lDim * 2, d] [lDim, d] := by
  rcases hrel with ⟨a0, a1, hs⟩
  have ha0 : a0.shape = [lDim, d] := hs.source0_shape
  have ha1 : a1.shape = [lDim, d] := hs.source1_shape
  refine ⟨fw_sigmoid a0, fw_sigmoid a1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ZigzagCuWF_unary_cp2 fw_sigmoid fw_sigmoid_shape (decodeCuSeqlens cu)
      a0 a1 lDim d hs.cu_wf ha0 ha1⟩
  · rw [hs.full_value]
    exact unary_allGather0_commute_cp2 fw_sigmoid sigmoidScalar
      fw_sigmoid_shape fw_sigmoid_valAt a0 a1 lDim d hl hd ha0 ha1
  · rw [hs.rank0_value]
    exact unary_shuffle_collective_cp2 fw_sigmoid sigmoidScalar
      fw_sigmoid_shape fw_sigmoid_valAt
      a0 a1 (decodeCuSeqlens cu) lDim d 0 hl hd (by decide) hs.cu_wf ha0 ha1
  · rw [hs.rank1_value]
    exact unary_shuffle_collective_cp2 fw_sigmoid sigmoidScalar
      fw_sigmoid_shape fw_sigmoid_valAt
      a0 a1 (decodeCuSeqlens cu) lDim d 1 hl hd (by decide) hs.cu_wf ha0 ha1
  · rw [fw_sigmoid_shape]; exact hs.full_shape
  · rw [fw_sigmoid_shape, ha0]
  · rw [fw_sigmoid_shape, ha1]
  · rw [fw_sigmoid_shape]; exact hs.rank0_shape
  · rw [fw_sigmoid_shape]; exact hs.rank1_shape

/-! ## (2) `fw_swiglu` (`OpName.FW_swiglu`) -/

/-- Two CP2 zigzag tensors sharing the **same** `cu` metadata can be combined by
the gated SiLU activation `swiglu(gate, up) = silu(gate) ⊙ up`, and the result is
again in CP2 zigzag layout with that same `cu`. -/
theorem swiglu
    {fullG zG0 zG1 fullU zU0 zU1 cu : Tensor} (lDim d : Nat)
    (hG : Zigzag2Rel fullG zG0 zG1 cu [lDim * 2, d] [lDim, d])
    (hU : Zigzag2Rel fullU zU0 zU1 cu [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    Zigzag2Rel (fw_swiglu fullG fullU) (fw_swiglu zG0 zU0) (fw_swiglu zG1 zU1)
      cu [lDim * 2, d] [lDim, d] := by
  have hval : ∀ (x y : Tensor) (a b idx : Nat), x.shape = [a, b] →
      y.shape = [a, b] → idx < a * b →
      valAt (fw_swiglu x y) idx =
        siluScalar (valAt x idx) * valAt y idx := by
    intro x y a b idx _hx hy hidx
    exact fw_swiglu_valAt x y idx (by rw [hy, prodShape_2d']; exact hidx)
  have hzero : siluScalar 0 * 0 = 0 := by rw [mul_zero]
  rcases hG with ⟨a0, a1, hAs⟩
  rcases hU with ⟨b0, b1, hBs⟩
  have ha0 : a0.shape = [lDim, d] := hAs.source0_shape
  have ha1 : a1.shape = [lDim, d] := hAs.source1_shape
  have hb0 : b0.shape = [lDim, d] := hBs.source0_shape
  have hb1 : b1.shape = [lDim, d] := hBs.source1_shape
  refine ⟨fw_swiglu a0 b0, fw_swiglu a1 b1, ?_, ?_, ?_, ?_,
    fw_swiglu_shape_of_shapes a0 b0 [lDim, d] ha0 hb0,
    fw_swiglu_shape_of_shapes a1 b1 [lDim, d] ha1 hb1, ?_, ?_,
    ZigzagCuWF_binary_cp2 fw_swiglu fw_swiglu_shape_of_shapes
      (decodeCuSeqlens cu) a0 a1 b0 b1 lDim d hAs.cu_wf ha0 ha1 hb0 hb1⟩
  · rw [hAs.full_value, hBs.full_value]
    exact binary_allGather0_commute_cp2 fw_swiglu (fun a b => siluScalar a * b)
      fw_swiglu_shape_of_shapes hval a0 a1 b0 b1 lDim d hl hd ha0 ha1 hb0 hb1
  · rw [hAs.rank0_value, hBs.rank0_value]
    exact binary_shuffle_collective_cp2 fw_swiglu (fun a b => siluScalar a * b)
      fw_swiglu_shape_of_shapes hval hzero a0 a1 b0 b1 (decodeCuSeqlens cu)
      lDim d 0 hl hd (by decide) ha0 ha1 hb0 hb1
  · rw [hAs.rank1_value, hBs.rank1_value]
    exact binary_shuffle_collective_cp2 fw_swiglu (fun a b => siluScalar a * b)
      fw_swiglu_shape_of_shapes hval hzero a0 a1 b0 b1 (decodeCuSeqlens cu)
      lDim d 1 hl hd (by decide) ha0 ha1 hb0 hb1
  · exact fw_swiglu_shape_of_shapes fullG fullU [lDim * 2, d]
      hAs.full_shape hBs.full_shape
  · exact fw_swiglu_shape_of_shapes zG0 zU0 [lDim, d]
      hAs.rank0_shape hBs.rank0_shape
  · exact fw_swiglu_shape_of_shapes zG1 zU1 [lDim, d]
      hAs.rank1_shape hBs.rank1_shape

/-! ## (3) `OpName.FW_mul`, denoted by `elemwiseMul`

The core library has **no** `fw_mul` identifier: `evalOp_fw_mul2` shows
`OpName.FW_mul` dispatches to `elemwiseMul`, so the statement uses that name. -/

/-- Elementwise multiplication of two CP2 zigzag tensors sharing the same `cu`
metadata stays in CP2 zigzag layout. -/
theorem mul
    {fullA zA0 zA1 fullB zB0 zB1 cu : Tensor} (lDim d : Nat)
    (hA : Zigzag2Rel fullA zA0 zA1 cu [lDim * 2, d] [lDim, d])
    (hB : Zigzag2Rel fullB zB0 zB1 cu [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    Zigzag2Rel (elemwiseMul fullA fullB) (elemwiseMul zA0 zB0)
      (elemwiseMul zA1 zB1) cu [lDim * 2, d] [lDim, d] := by
  have hval : ∀ (x y : Tensor) (a b idx : Nat), x.shape = [a, b] →
      y.shape = [a, b] → idx < a * b →
      valAt (elemwiseMul x y) idx = valAt x idx * valAt y idx := by
    intro x y a b idx hx hy hidx
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · exact absurd hidx (by rw [hb0, Nat.mul_zero]; omega)
    · exact elemwiseMul_valAt_2d x y a b idx hx hy hbpos hidx
  have hzero : (0 : Scalar) * 0 = 0 := by rw [mul_zero]
  rcases hA with ⟨a0, a1, hAs⟩
  rcases hB with ⟨b0, b1, hBs⟩
  have ha0 : a0.shape = [lDim, d] := hAs.source0_shape
  have ha1 : a1.shape = [lDim, d] := hAs.source1_shape
  have hb0 : b0.shape = [lDim, d] := hBs.source0_shape
  have hb1 : b1.shape = [lDim, d] := hBs.source1_shape
  refine ⟨elemwiseMul a0 b0, elemwiseMul a1 b1, ?_, ?_, ?_, ?_,
    elemwiseMul_shape_of_shapes' a0 b0 [lDim, d] ha0 hb0,
    elemwiseMul_shape_of_shapes' a1 b1 [lDim, d] ha1 hb1, ?_, ?_,
    ZigzagCuWF_binary_cp2 elemwiseMul elemwiseMul_shape_of_shapes'
      (decodeCuSeqlens cu) a0 a1 b0 b1 lDim d hAs.cu_wf ha0 ha1 hb0 hb1⟩
  · rw [hAs.full_value, hBs.full_value]
    exact binary_allGather0_commute_cp2 elemwiseMul (fun a b => a * b)
      elemwiseMul_shape_of_shapes' hval a0 a1 b0 b1 lDim d hl hd
      ha0 ha1 hb0 hb1
  · rw [hAs.rank0_value, hBs.rank0_value]
    exact binary_shuffle_collective_cp2 elemwiseMul (fun a b => a * b)
      elemwiseMul_shape_of_shapes' hval hzero a0 a1 b0 b1
      (decodeCuSeqlens cu) lDim d 0 hl hd (by decide) ha0 ha1 hb0 hb1
  · rw [hAs.rank1_value, hBs.rank1_value]
    exact binary_shuffle_collective_cp2 elemwiseMul (fun a b => a * b)
      elemwiseMul_shape_of_shapes' hval hzero a0 a1 b0 b1
      (decodeCuSeqlens cu) lDim d 1 hl hd (by decide) ha0 ha1 hb0 hb1
  · exact elemwiseMul_shape_of_shapes' fullA fullB [lDim * 2, d]
      hAs.full_shape hBs.full_shape
  · exact elemwiseMul_shape_of_shapes' zA0 zB0 [lDim, d]
      hAs.rank0_shape hBs.rank0_shape
  · exact elemwiseMul_shape_of_shapes' zA1 zB1 [lDim, d]
      hAs.rank1_shape hBs.rank1_shape

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
