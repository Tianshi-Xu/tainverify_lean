/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagRouterRel

/-!
# The MoE expert layer `fw_all2all_moe_gmm` preserves the CP2 zigzag layout

The generated graph runs the MoE expert FFN at SM node 526, with parameters
`[64, 0, 64, 8]`, i.e. `numExperts = 64`, `localExpertStart = 0`,
`localExpertEnd = 64`, `topK = 8`.  The operator consumes three token-indexed
streams — the hidden states `x : [l, hModel]`, and the router metadata
`routing_probs, routing_map : [l, numExperts]` — plus two *replicated* expert
weights `w13`, `w2`.

## Row locality audit

`fw_all2all_moe_gmm` (`denote/Denote.lean:1958`) is **row local** in all three
token-indexed inputs:

* the output is `Tensor.mkShape [lDim, hModel] (fun outIdx => …)` with
  `l := outIdx.1 / hModel` the token index and `h := outIdx.1 % hModel`;
* every read of `input` in the body is `valAt input (l * hModel + k)` with
  `k ∈ [0, hModel)` — no other token row occurs;
* every read of the router metadata is `valAt routing_map (l * numExp + e)` and
  `valAt routing_probs (l * numExp + e)`, sharing the *same* `l`;
* the three nested `Finset.sum`s range over experts, the inner hidden dim, and
  the model dim — **none** of them ranges over the token dimension.

The Python `permute → all-to-all → unpermute` triple is already algebraically
eliminated in the Lean model (see the comment at `denote/Denote.lean:1932`), so
there is no cross-token movement to account for.  `localExpertStart` is an
*expert*-dimension offset and never shifts token rows.

## Why the differing trailing dimensions are harmless

`fw_maybe_shuffle_collective` (`denote/ZigzagCollective.lean:50`) picks its
source purely through `zigzagPos cu cpSize cpRank token`; the `hiddenStride`
only re-expands the chosen token row.  The token stream has tail `[hModel]`
while the router metadata has tail `[numExperts]`, but as long as the *token*
argument is the same output row `l` and the metadata `cu` is shared, the
permutation `g = zigzagPos cu 2 rank l` is literally the same natural number
for all three streams.  The proofs below therefore factor through a single
`Row3Local*` abstraction that keeps one `g` and expands it into the three
per-stream flat offsets `g % lDim * hModel + k` and `g % lDim * numExp + e`.

## The out-of-range branch

As for the router (`ZigzagRouterRel.lean`), we do **not** pretend that the
degenerate `zigzagPos … / lDim ≥ 2` branch closes by itself: the MoE body is not
linear in its inputs (`min`/`max` clamps, `siluScalar`, the `mask = 0` test), so
an all-zero source row does not produce an all-zero output row in general.  The
generic shuffle lemma takes the honest hypothesis `hpos` and the `Zigzag2Rel`
propagation theorem discharges it from `decodeCuSeqlens cu = [0, 2 * lDim]` via
`zigzagPos_single_lt`.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-! ## Reading one row of a faithful CP2 shuffle -/

/-- Reading token row `row` of a CP2 shuffle is reading token row
`g % lDim` of source shard `g / lDim`, where `g = zigzagPos cu 2 rank row`.
This is a definitional unfolding of `gatherFromRank`; in particular it needs
no in-range hypothesis on `g`. -/
theorem shuffle_row_read (s0 s1 : Tensor) (cu : List Nat)
    (d lDim rank row : Nat)
    (hd : 0 < d) (hrank : rank < 2) (hrow : row < lDim)
    (hs0 : s0.shape = [lDim, d]) (hs1 : s1.shape = [lDim, d]) :
    ∀ j, j < d →
      valAt (fw_maybe_shuffle_collective [s0, s1] cu 2 rank) (row * d + j) =
        valAt ([s0, s1].getD (zigzagPos cu 2 rank row / lDim) (zeroTensor []))
          (zigzagPos cu 2 rank row % lDim * d + j) := by
  have hlocal : ([s0, s1].getD rank (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hs0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
  intro j hj
  rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
    (by rw [hlocal, prodShape_2d']
        calc row * d + j < row * d + d := Nat.add_lt_add_left hj _
          _ = (row + 1) * d := by ring
          _ ≤ lDim * d := Nat.mul_le_mul_right _ hrow)]
  simp only [hlocal, List.tail_cons, prodShape, List.foldl,
    Nat.one_mul, List.getD_cons_zero]
  rw [show row * d + j = j + d * row by ring,
    Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  unfold gatherFromRank
  rfl

/-! ## Abstract row locality for a ternary token-indexed operator -/

/-- `f` maps a `[a, d1]` token stream plus two `[a, d2]` metadata streams to a
`[a, e]` output. -/
def Row3LocalShape (f : Tensor → Tensor → Tensor → Tensor) (d1 d2 e : Nat) :
    Prop :=
  ∀ (a : Nat) (x y z : Tensor), x.shape = [a, d1] → y.shape = [a, d2] →
    z.shape = [a, d2] → (f x y z).shape = [a, e]

/-- Output row `ix` of `f x y z` is determined by row `ix` of each of the three
inputs. -/
def Row3LocalCongr (f : Tensor → Tensor → Tensor → Tensor) (d1 d2 e : Nat) :
    Prop :=
  ∀ (a b : Nat) (x y z x' y' z' : Tensor) (ix iy c : Nat),
    x.shape = [a, d1] → y.shape = [a, d2] → z.shape = [a, d2] →
    x'.shape = [b, d1] → y'.shape = [b, d2] → z'.shape = [b, d2] →
    ix < a → iy < b → c < e →
    (∀ j, j < d1 → valAt x (ix * d1 + j) = valAt x' (iy * d1 + j)) →
    (∀ j, j < d2 → valAt y (ix * d2 + j) = valAt y' (iy * d2 + j)) →
    (∀ j, j < d2 → valAt z (ix * d2 + j) = valAt z' (iy * d2 + j)) →
    valAt (f x y z) (ix * e + c) = valAt (f x' y' z') (iy * e + c)

/-! ## Commutation with the ordinary dim-0 all-gather -/

theorem row3Local_allGather0_commute_2
    (f : Tensor → Tensor → Tensor → Tensor) (d1 d2 e lDim : Nat)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (he : 0 < e) (hl : 0 < lDim)
    (hshape : Row3LocalShape f d1 d2 e) (hcongr : Row3LocalCongr f d1 d2 e)
    (x0 x1 y0 y1 z0 z1 : Tensor)
    (hx0 : x0.shape = [lDim, d1]) (hx1 : x1.shape = [lDim, d1])
    (hy0 : y0.shape = [lDim, d2]) (hy1 : y1.shape = [lDim, d2])
    (hz0 : z0.shape = [lDim, d2]) (hz1 : z1.shape = [lDim, d2]) :
    f (allGatherPrimDimN 0 2 0 [x0, x1]) (allGatherPrimDimN 0 2 0 [y0, y1])
        (allGatherPrimDimN 0 2 0 [z0, z1]) =
      allGatherPrimDimN 0 2 0 [f x0 y0 z0, f x1 y1 z1] := by
  have hheadX : (([x0, x1].head?.map (fun t => t.shape)).getD []) = [lDim, d1] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hx0]
  have hheadY : (([y0, y1].head?.map (fun t => t.shape)).getD []) = [lDim, d2] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hy0]
  have hheadZ : (([z0, z1].head?.map (fun t => t.shape)).getD []) = [lDim, d2] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hz0]
  have hF0 : (f x0 y0 z0).shape = [lDim, e] := hshape lDim x0 y0 z0 hx0 hy0 hz0
  have hF1 : (f x1 y1 z1).shape = [lDim, e] := hshape lDim x1 y1 z1 hx1 hy1 hz1
  have hheadF : (([f x0 y0 z0, f x1 y1 z1].head?.map (fun t => t.shape)).getD []) =
      [lDim, e] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hF0]
  have hgetX : ∀ r (_ : r < 2),
      ([x0, x1].getD r (zeroTensor [lDim, d1])).shape = [lDim, d1] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hx0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hx1
  have hgetY : ∀ r (_ : r < 2),
      ([y0, y1].getD r (zeroTensor [lDim, d2])).shape = [lDim, d2] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hy0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hy1
  have hgetZ : ∀ r (_ : r < 2),
      ([z0, z1].getD r (zeroTensor [lDim, d2])).shape = [lDim, d2] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hz0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hz1
  have hgetF : ∀ r (_ : r < 2),
      ([f x0 y0 z0, f x1 y1 z1].getD r (zeroTensor [lDim, e])).shape =
        [lDim, e] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hF0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hF1
  have hGX : (allGatherPrimDimN 0 2 0 [x0, x1]).shape = [lDim * 2, d1] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d1] hheadX]
    simp only [List.set, List.getD_cons_zero]
  have hGY : (allGatherPrimDimN 0 2 0 [y0, y1]).shape = [lDim * 2, d2] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d2] hheadY]
    simp only [List.set, List.getD_cons_zero]
  have hGZ : (allGatherPrimDimN 0 2 0 [z0, z1]).shape = [lDim * 2, d2] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d2] hheadZ]
    simp only [List.set, List.getD_cons_zero]
  have hGF : (allGatherPrimDimN 0 2 0 [f x0 y0 z0, f x1 y1 z1]).shape =
      [lDim * 2, e] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, e] hheadF]
    simp only [List.set, List.getD_cons_zero]
  have hlhs : (f (allGatherPrimDimN 0 2 0 [x0, x1])
      (allGatherPrimDimN 0 2 0 [y0, y1])
      (allGatherPrimDimN 0 2 0 [z0, z1])).shape = [lDim * 2, e] :=
    hshape (lDim * 2) _ _ _ hGX hGY hGZ
  refine Tensor.ext ?_ ?_
  · rw [hlhs, hGF]
  · intro idx hidx
    rw [hlhs, prodShape_2d'] at hidx
    set row := idx / e with hrowdef
    set c := idx % e with hcdef
    have hc : c < e := Nat.mod_lt _ he
    have hrow : row < lDim * 2 := (Nat.div_lt_iff_lt_mul he).mpr hidx
    have hidxEq : idx = row * e + c := by
      rw [hrowdef, hcdef]; exact (Nat.div_add_mod' idx e).symm
    set r := row / lDim with hrdef
    set i := row % lDim with hidef
    have hi : i < lDim := Nat.mod_lt _ hl
    have hr : r < 2 := by
      rw [hrdef]
      exact (Nat.div_lt_iff_lt_mul hl).mpr (by rw [Nat.mul_comm]; exact hrow)
    have hrowEq : row = r * lDim + i := by
      rw [hrdef, hidef]; exact (Nat.div_add_mod' row lDim).symm
    have hrowX : ∀ j, j < d1 →
        valAt (allGatherPrimDimN 0 2 0 [x0, x1]) (row * d1 + j) =
          valAt ([x0, x1].getD r (zeroTensor [lDim, d1])) (i * d1 + j) := by
      intro j hj
      rw [hrowEq]
      exact allGatherPrimDimN0_valAt 2 lDim d1 [x0, x1] (by decide) hl hd1
        hheadX hgetX r hr i hi j hj
    have hrowY : ∀ j, j < d2 →
        valAt (allGatherPrimDimN 0 2 0 [y0, y1]) (row * d2 + j) =
          valAt ([y0, y1].getD r (zeroTensor [lDim, d2])) (i * d2 + j) := by
      intro j hj
      rw [hrowEq]
      exact allGatherPrimDimN0_valAt 2 lDim d2 [y0, y1] (by decide) hl hd2
        hheadY hgetY r hr i hi j hj
    have hrowZ : ∀ j, j < d2 →
        valAt (allGatherPrimDimN 0 2 0 [z0, z1]) (row * d2 + j) =
          valAt ([z0, z1].getD r (zeroTensor [lDim, d2])) (i * d2 + j) := by
      intro j hj
      rw [hrowEq]
      exact allGatherPrimDimN0_valAt 2 lDim d2 [z0, z1] (by decide) hl hd2
        hheadZ hgetZ r hr i hi j hj
    rw [hidxEq]
    rw [hcongr (lDim * 2) lDim _ _ _
      ([x0, x1].getD r (zeroTensor [lDim, d1]))
      ([y0, y1].getD r (zeroTensor [lDim, d2]))
      ([z0, z1].getD r (zeroTensor [lDim, d2])) row i c
      hGX hGY hGZ (hgetX r hr) (hgetY r hr) (hgetZ r hr) hrow hi hc
      hrowX hrowY hrowZ]
    rw [hrowEq]
    rw [allGatherPrimDimN0_valAt 2 lDim e [f x0 y0 z0, f x1 y1 z1]
      (by decide) hl he hheadF hgetF r hr i hi c hc]
    interval_cases r
    · simp only [List.getD_cons_zero]
    · simp only [List.getD_cons_succ, List.getD_cons_zero]

/-! ## Commutation with the faithful CP2 shuffle -/

theorem row3Local_shuffle_collective_cp2
    (f : Tensor → Tensor → Tensor → Tensor) (d1 d2 e lDim rank : Nat)
    (cu : List Nat)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (he : 0 < e) (hl : 0 < lDim) (hrank : rank < 2)
    (hshape : Row3LocalShape f d1 d2 e) (hcongr : Row3LocalCongr f d1 d2 e)
    (x0 x1 y0 y1 z0 z1 : Tensor)
    (hx0 : x0.shape = [lDim, d1]) (hx1 : x1.shape = [lDim, d1])
    (hy0 : y0.shape = [lDim, d2]) (hy1 : y1.shape = [lDim, d2])
    (hz0 : z0.shape = [lDim, d2]) (hz1 : z1.shape = [lDim, d2])
    (hpos : ∀ t, t < lDim → zigzagPos cu 2 rank t < 2 * lDim) :
    f (fw_maybe_shuffle_collective [x0, x1] cu 2 rank)
        (fw_maybe_shuffle_collective [y0, y1] cu 2 rank)
        (fw_maybe_shuffle_collective [z0, z1] cu 2 rank) =
      fw_maybe_shuffle_collective [f x0 y0 z0, f x1 y1 z1] cu 2 rank := by
  have hF0 : (f x0 y0 z0).shape = [lDim, e] := hshape lDim x0 y0 z0 hx0 hy0 hz0
  have hF1 : (f x1 y1 z1).shape = [lDim, e] := hshape lDim x1 y1 z1 hx1 hy1 hz1
  have hlocalX : ([x0, x1].getD rank (zeroTensor [])).shape = [lDim, d1] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hx0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hx1
  have hlocalY : ([y0, y1].getD rank (zeroTensor [])).shape = [lDim, d2] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hy0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hy1
  have hlocalZ : ([z0, z1].getD rank (zeroTensor [])).shape = [lDim, d2] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hz0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hz1
  have hlocalF : ([f x0 y0 z0, f x1 y1 z1].getD rank (zeroTensor [])).shape =
      [lDim, e] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hF0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hF1
  have hSX : (fw_maybe_shuffle_collective [x0, x1] cu 2 rank).shape =
      [lDim, d1] := by rw [fw_maybe_shuffle_collective_shape]; exact hlocalX
  have hSY : (fw_maybe_shuffle_collective [y0, y1] cu 2 rank).shape =
      [lDim, d2] := by rw [fw_maybe_shuffle_collective_shape]; exact hlocalY
  have hSZ : (fw_maybe_shuffle_collective [z0, z1] cu 2 rank).shape =
      [lDim, d2] := by rw [fw_maybe_shuffle_collective_shape]; exact hlocalZ
  have hlhs : (f (fw_maybe_shuffle_collective [x0, x1] cu 2 rank)
      (fw_maybe_shuffle_collective [y0, y1] cu 2 rank)
      (fw_maybe_shuffle_collective [z0, z1] cu 2 rank)).shape = [lDim, e] :=
    hshape lDim _ _ _ hSX hSY hSZ
  refine Tensor.ext ?_ ?_
  · rw [hlhs, fw_maybe_shuffle_collective_shape, hlocalF]
  · intro idx hidx
    rw [hlhs, prodShape_2d'] at hidx
    set row := idx / e with hrowdef
    set c := idx % e with hcdef
    have hc : c < e := Nat.mod_lt _ he
    have hrow : row < lDim := (Nat.div_lt_iff_lt_mul he).mpr hidx
    have hidxEq : idx = row * e + c := by
      rw [hrowdef, hcdef]; exact (Nat.div_add_mod' idx e).symm
    -- The single shared permutation.
    set g := zigzagPos cu 2 rank row with hgdef
    have hglt : g < 2 * lDim := hpos row hrow
    have hi : g % lDim < lDim := Nat.mod_lt _ hl
    have hr : g / lDim < 2 := by
      refine (Nat.div_lt_iff_lt_mul hl).mpr ?_
      omega
    have hr2 : g / lDim = 0 ∨ g / lDim = 1 := lt_two_cases _ hr
    have hgetXs : ([x0, x1].getD (g / lDim) (zeroTensor [])).shape =
        [lDim, d1] := by
      rcases hr2 with h | h
      · rw [h]; simpa only [List.getD_cons_zero] using hx0
      · rw [h]; simpa only [List.getD_cons_succ, List.getD_cons_zero] using hx1
    have hgetYs : ([y0, y1].getD (g / lDim) (zeroTensor [])).shape =
        [lDim, d2] := by
      rcases hr2 with h | h
      · rw [h]; simpa only [List.getD_cons_zero] using hy0
      · rw [h]; simpa only [List.getD_cons_succ, List.getD_cons_zero] using hy1
    have hgetZs : ([z0, z1].getD (g / lDim) (zeroTensor [])).shape =
        [lDim, d2] := by
      rcases hr2 with h | h
      · rw [h]; simpa only [List.getD_cons_zero] using hz0
      · rw [h]; simpa only [List.getD_cons_succ, List.getD_cons_zero] using hz1
    have hrowX := shuffle_row_read x0 x1 cu d1 lDim rank row hd1 hrank hrow hx0 hx1
    have hrowY := shuffle_row_read y0 y1 cu d2 lDim rank row hd2 hrank hrow hy0 hy1
    have hrowZ := shuffle_row_read z0 z1 cu d2 lDim rank row hd2 hrank hrow hz0 hz1
    rw [← hgdef] at hrowX hrowY hrowZ
    rw [hidxEq]
    rw [hcongr lDim lDim _ _ _
      ([x0, x1].getD (g / lDim) (zeroTensor []))
      ([y0, y1].getD (g / lDim) (zeroTensor []))
      ([z0, z1].getD (g / lDim) (zeroTensor [])) row (g % lDim) c
      hSX hSY hSZ hgetXs hgetYs hgetZs hrow hi hc hrowX hrowY hrowZ]
    rw [shuffle_row_read (f x0 y0 z0) (f x1 y1 z1) cu e lDim rank row
      he hrank hrow hF0 hF1 c hc]
    rw [← hgdef]
    rcases hr2 with h | h
    · rw [h]; simp only [List.getD_cons_zero]
    · rw [h]; simp only [List.getD_cons_succ, List.getD_cons_zero]

/-! ## Metadata well-formedness transports along a ternary row-local operator -/

theorem ZigzagCuWF.row3Local_cp2
    (f : Tensor → Tensor → Tensor → Tensor) (cu : List Nat)
    (x0 x1 y0 y1 z0 z1 : Tensor) (lDim d1 d2 e : Nat)
    (hshape : Row3LocalShape f d1 d2 e)
    (hwf : ZigzagCuWF cu [x0, x1] 2)
    (hx0 : x0.shape = [lDim, d1]) (hx1 : x1.shape = [lDim, d1])
    (hy0 : y0.shape = [lDim, d2]) (hy1 : y1.shape = [lDim, d2])
    (hz0 : z0.shape = [lDim, d2]) (hz1 : z1.shape = [lDim, d2]) :
    ZigzagCuWF cu [f x0 y0 z0, f x1 y1 z1] 2 := by
  have hF0 : (f x0 y0 z0).shape = [lDim, e] := hshape lDim x0 y0 z0 hx0 hy0 hz0
  have hF1 : (f x1 y1 z1).shape = [lDim, e] := hshape lDim x1 y1 z1 hx1 hy1 hz1
  refine ⟨hwf.cp_pos, rfl, hwf.cu_starts_zero, hwf.cu_has_endpoint,
    hwf.monotone, hwf.divisible, ?_, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rw [hF0]; exact List.cons_ne_nil _ _
    · rw [hF1]; exact List.cons_ne_nil _ _
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rfl
    · simp only [List.getD_cons_zero]
      rw [hF1, hF0]
  · have h := hwf.local_tokens
    simp only [List.getD_cons_zero, hx0] at h
    simpa only [List.getD_cons_zero, hF0] using h

namespace Zigzag2Rel

/-- **Master propagation lemma for ternary token-indexed row-local operators.**

The three input relations must share the *same* metadata tensor `cu`: this is
exactly what makes the token permutation `zigzagPos (decodeCuSeqlens cu) 2 rank`
common to all three streams, even though their trailing dimensions differ. -/
theorem row3Local
    {fx fy fz zx0 zx1 zy0 zy1 zz0 zz1 cu : Tensor}
    (f : Tensor → Tensor → Tensor → Tensor) (d1 d2 e lDim : Nat)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (he : 0 < e) (hl : 0 < lDim)
    (heven : lDim % 2 = 0)
    (hshape : Row3LocalShape f d1 d2 e) (hcongr : Row3LocalCongr f d1 d2 e)
    (hrelX : Zigzag2Rel fx zx0 zx1 cu [lDim * 2, d1] [lDim, d1])
    (hrelY : Zigzag2Rel fy zy0 zy1 cu [lDim * 2, d2] [lDim, d2])
    (hrelZ : Zigzag2Rel fz zz0 zz1 cu [lDim * 2, d2] [lDim, d2])
    (hdec : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Zigzag2Rel (f fx fy fz) (f zx0 zy0 zz0) (f zx1 zy1 zz1) cu
      [lDim * 2, e] [lDim, e] := by
  rcases hrelX with ⟨sx0, sx1, hsx⟩
  rcases hrelY with ⟨sy0, sy1, hsy⟩
  rcases hrelZ with ⟨sz0, sz1, hsz⟩
  have hx0 : sx0.shape = [lDim, d1] := hsx.source0_shape
  have hx1 : sx1.shape = [lDim, d1] := hsx.source1_shape
  have hy0 : sy0.shape = [lDim, d2] := hsy.source0_shape
  have hy1 : sy1.shape = [lDim, d2] := hsy.source1_shape
  have hz0 : sz0.shape = [lDim, d2] := hsz.source0_shape
  have hz1 : sz1.shape = [lDim, d2] := hsz.source1_shape
  have hpos : ∀ rank, rank < 2 → ∀ t, t < lDim →
      zigzagPos (decodeCuSeqlens cu) 2 rank t < 2 * lDim := by
    intro rank hrank t ht
    rw [hdec]
    exact zigzagPos_single_lt lDim rank t heven hrank ht
  refine ⟨f sx0 sy0 sz0, f sx1 sy1 sz1, ?_, ?_, ?_, ?_,
    hshape lDim sx0 sy0 sz0 hx0 hy0 hz0, hshape lDim sx1 sy1 sz1 hx1 hy1 hz1,
    ?_, ?_,
    ZigzagCuWF.row3Local_cp2 f _ sx0 sx1 sy0 sy1 sz0 sz1 lDim d1 d2 e hshape
      hsx.cu_wf hx0 hx1 hy0 hy1 hz0 hz1⟩
  · rw [hsx.full_value, hsy.full_value, hsz.full_value]
    exact row3Local_allGather0_commute_2 f d1 d2 e lDim hd1 hd2 he hl
      hshape hcongr sx0 sx1 sy0 sy1 sz0 sz1 hx0 hx1 hy0 hy1 hz0 hz1
  · rw [hsx.rank0_value, hsy.rank0_value, hsz.rank0_value]
    exact row3Local_shuffle_collective_cp2 f d1 d2 e lDim 0
      (decodeCuSeqlens cu) hd1 hd2 he hl (by decide) hshape hcongr
      sx0 sx1 sy0 sy1 sz0 sz1 hx0 hx1 hy0 hy1 hz0 hz1 (hpos 0 (by decide))
  · rw [hsx.rank1_value, hsy.rank1_value, hsz.rank1_value]
    exact row3Local_shuffle_collective_cp2 f d1 d2 e lDim 1
      (decodeCuSeqlens cu) hd1 hd2 he hl (by decide) hshape hcongr
      sx0 sx1 sy0 sy1 sz0 sz1 hx0 hx1 hy0 hy1 hz0 hz1 (hpos 1 (by decide))
  · exact hshape (lDim * 2) fx fy fz hsx.full_shape hsy.full_shape hsz.full_shape
  · exact hshape lDim zx0 zy0 zz0 hsx.rank0_shape hsy.rank0_shape hsz.rank0_shape
  · exact hshape lDim zx1 zy1 zz1 hsx.rank1_shape hsy.rank1_shape hsz.rank1_shape

end Zigzag2Rel

/-! ## Row-local analysis of `fw_all2all_moe_gmm` -/

/-- The MoE expert-sum body at a fixed `(l, h_col, eLocal)`.  This mirrors the
`moe_gmm_term` abbreviation used in `Pattern_1.lean` (which is `private`, hence
re-declared here). -/
noncomputable def moeGmmTerm
    (input rp rm w13 w2 : Tensor)
    (numExp start eLocal l h_col hModel h_inner w13Mid : Nat)
    (swigluLimit : Scalar) : Scalar :=
  let e := start + eLocal
  let mask := valAt rm (l * numExp + e)
  if mask = 0 then 0
  else
    let prob := valAt rp (l * numExp + e)
    prob * ∑ d ∈ Finset.range h_inner,
      let gateRaw := ∑ k ∈ Finset.range hModel,
        valAt input (l * hModel + k) *
        valAt w13 ((eLocal * w13Mid + d) * hModel + k)
      let upRaw := ∑ k ∈ Finset.range hModel,
        valAt input (l * hModel + k) *
        valAt w13 ((eLocal * w13Mid + (h_inner + d)) * hModel + k)
      let gateClamped := min swigluLimit gateRaw
      let upClamped   := max (-swigluLimit) (min swigluLimit upRaw)
      let swigluVal   := siluScalar gateClamped * upClamped
      swigluVal * valAt w2 ((eLocal * hModel + h_col) * h_inner + d)

/-- Cross-row congruence of the expert-sum body: only rows `l₁` / `l₂` of the
three token-indexed inputs are read. -/
theorem moeGmmTerm_congr
    (input₁ rp₁ rm₁ input₂ rp₂ rm₂ w13 w2 : Tensor)
    (numExp start eLocal l₁ l₂ h_col hModel h_inner w13Mid : Nat)
    (swigluLimit : Scalar)
    (hmask : valAt rm₁ (l₁ * numExp + (start + eLocal)) =
      valAt rm₂ (l₂ * numExp + (start + eLocal)))
    (hprob : valAt rp₁ (l₁ * numExp + (start + eLocal)) =
      valAt rp₂ (l₂ * numExp + (start + eLocal)))
    (hinput : ∀ k, k < hModel →
      valAt input₁ (l₁ * hModel + k) = valAt input₂ (l₂ * hModel + k)) :
    moeGmmTerm input₁ rp₁ rm₁ w13 w2 numExp start eLocal l₁ h_col hModel
        h_inner w13Mid swigluLimit
      = moeGmmTerm input₂ rp₂ rm₂ w13 w2 numExp start eLocal l₂ h_col hModel
        h_inner w13Mid swigluLimit := by
  unfold moeGmmTerm
  simp only [hmask]
  by_cases h : valAt rm₂ (l₂ * numExp + (start + eLocal)) = 0
  · simp only [h, if_pos]
  · simp only [h, if_false]
    rw [hprob]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro d _
    have hgate : (∑ k ∈ Finset.range hModel,
        valAt input₁ (l₁ * hModel + k) *
        valAt w13 ((eLocal * w13Mid + d) * hModel + k))
        = ∑ k ∈ Finset.range hModel,
          valAt input₂ (l₂ * hModel + k) *
          valAt w13 ((eLocal * w13Mid + d) * hModel + k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hinput k (Finset.mem_range.mp hk)]
    have hup : (∑ k ∈ Finset.range hModel,
        valAt input₁ (l₁ * hModel + k) *
        valAt w13 ((eLocal * w13Mid + (h_inner + d)) * hModel + k))
        = ∑ k ∈ Finset.range hModel,
          valAt input₂ (l₂ * hModel + k) *
          valAt w13 ((eLocal * w13Mid + (h_inner + d)) * hModel + k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hinput k (Finset.mem_range.mp hk)]
    simp only [hgate, hup]

/-- Value of `fw_all2all_moe_gmm` at flat index `l * hModel + h_col`. -/
theorem fw_all2all_moe_gmm_valAt'
    (input rp rm w13 w2 : Tensor)
    (L hModel numExp E_total start endE topK t_dim d_dim : Nat)
    (hhModel : 0 < hModel)
    (ht_even : t_dim = 2 * d_dim)
    (hinput_shape : input.shape = [L, hModel])
    (hrp_shape : rp.shape = [L, numExp])
    (hw13_shape : w13.shape = [E_total, t_dim, hModel])
    (l : Nat) (hl : l < L) (h_col : Nat) (hh_col : h_col < hModel)
    (swigluLimit : Scalar) :
    valAt (fw_all2all_moe_gmm input rp rm w13 w2 numExp start endE topK
        swigluLimit) (l * hModel + h_col)
      = ∑ eLocal ∈ Finset.range (endE - start),
          moeGmmTerm input rp rm w13 w2 numExp start eLocal l h_col hModel
            d_dim t_dim swigluLimit := by
  unfold fw_all2all_moe_gmm
  simp only [Tensor.mkShape, valAt]
  have hbound : l * hModel + h_col <
      prodShape [(input.shape.head?).getD 0,
        (input.shape.reverse.head?).getD 0] := by
    rw [hinput_shape]
    simp only [List.head?_cons, Option.getD_some, List.reverse_cons,
      List.reverse_nil, List.nil_append, prodShape, List.foldl, Nat.one_mul]
    calc l * hModel + h_col < l * hModel + hModel := by omega
      _ = (l + 1) * hModel := by ring
      _ ≤ L * hModel := Nat.mul_le_mul_right _ (by omega)
  rw [dif_pos hbound]
  have hModel_eq : (input.shape.reverse.head?).getD 0 = hModel := by
    rw [hinput_shape]; rfl
  have hw13Mid_eq : (w13.shape.drop 1).head?.getD 0 = t_dim := by
    rw [hw13_shape]; rfl
  have hnumExp_eq : (rp.shape.drop 1).head?.getD 0 = numExp := by
    rw [hrp_shape]; rfl
  have hh_inner_eq : t_dim / 2 = d_dim := by rw [ht_even]; omega
  have hh_eq : (l * hModel + h_col) % hModel = h_col := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hh_col]
  have hl'_eq : (l * hModel + h_col) / hModel = l := by
    rw [Nat.add_comm, Nat.add_mul_div_right h_col l hhModel,
      Nat.div_eq_of_lt hh_col, Nat.zero_add]
  unfold moeGmmTerm
  simp only [hModel_eq, hw13Mid_eq, hnumExp_eq, hh_inner_eq, hh_eq, hl'_eq]
  simp only [valAt]

theorem fw_all2all_moe_gmm_shape'
    (input rp rm w13 w2 : Tensor) (a hModel numExp start endE topK : Nat)
    (swigluLimit : Scalar) (hinput_shape : input.shape = [a, hModel]) :
    (fw_all2all_moe_gmm input rp rm w13 w2 numExp start endE topK
        swigluLimit).shape = [a, hModel] := by
  unfold fw_all2all_moe_gmm
  simp only [Tensor.mkShape, hinput_shape]
  rfl

/-! ## The two row-local facts for the concrete operator -/

theorem Row3LocalShape_moe_gmm (hModel numExp topK : Nat) (w13 w2 : Tensor)
    (swigluLimit : Scalar) :
    Row3LocalShape (fun x y z => fw_all2all_moe_gmm x y z w13 w2 numExp 0
      numExp topK swigluLimit) hModel numExp hModel :=
  fun a x y z hx _ _ =>
    fw_all2all_moe_gmm_shape' x y z w13 w2 a hModel numExp 0 numExp topK
      swigluLimit hx

set_option maxHeartbeats 1600000 in
theorem Row3LocalCongr_moe_gmm (hModel numExp topK E_total t_dim d_dim : Nat)
    (w13 w2 : Tensor) (swigluLimit : Scalar)
    (hhModel : 0 < hModel) (ht_even : t_dim = 2 * d_dim)
    (hw13_shape : w13.shape = [E_total, t_dim, hModel]) :
    Row3LocalCongr (fun x y z => fw_all2all_moe_gmm x y z w13 w2 numExp 0
      numExp topK swigluLimit) hModel numExp hModel := by
  intro a b x y z x' y' z' ix iy c hx hy _ hx' hy' _ hix hiy hc
    hrowX hrowY hrowZ
  change valAt (fw_all2all_moe_gmm x y z w13 w2 numExp 0 numExp topK swigluLimit)
      (ix * hModel + c) =
    valAt (fw_all2all_moe_gmm x' y' z' w13 w2 numExp 0 numExp topK swigluLimit)
      (iy * hModel + c)
  rw [fw_all2all_moe_gmm_valAt' x y z w13 w2 a hModel numExp E_total 0 numExp
    topK t_dim d_dim hhModel ht_even hx hy hw13_shape ix hix c hc swigluLimit]
  rw [fw_all2all_moe_gmm_valAt' x' y' z' w13 w2 b hModel numExp E_total 0 numExp
    topK t_dim d_dim hhModel ht_even hx' hy' hw13_shape iy hiy c hc swigluLimit]
  refine Finset.sum_congr rfl ?_
  intro eLocal heL
  have heL' : eLocal < numExp := by
    have := Finset.mem_range.mp heL
    omega
  have h0 : (0 : Nat) + eLocal = eLocal := Nat.zero_add eLocal
  refine moeGmmTerm_congr x y z x' y' z' w13 w2 numExp 0 eLocal ix iy c
    hModel d_dim t_dim swigluLimit ?_ ?_ ?_
  · rw [h0]; exact hrowZ eLocal heL'
  · rw [h0]; exact hrowY eLocal heL'
  · intro k hk; exact hrowX k hk

/-! ## The bottom-level shuffle commute, stated concretely -/

theorem fw_all2all_moe_gmm_shuffle_collective_cp2
    (x0 x1 rp0 rp1 rm0 rm1 w13 w2 : Tensor) (cu : List Nat)
    (lDim hModel numExp topK E_total t_dim d_dim rank : Nat)
    (swigluLimit : Scalar)
    (hl : 0 < lDim) (hhModel : 0 < hModel) (hnE : 0 < numExp) (hrank : rank < 2)
    (ht_even : t_dim = 2 * d_dim)
    (hw13_shape : w13.shape = [E_total, t_dim, hModel])
    (hx0 : x0.shape = [lDim, hModel]) (hx1 : x1.shape = [lDim, hModel])
    (hrp0 : rp0.shape = [lDim, numExp]) (hrp1 : rp1.shape = [lDim, numExp])
    (hrm0 : rm0.shape = [lDim, numExp]) (hrm1 : rm1.shape = [lDim, numExp])
    (hpos : ∀ t, t < lDim → zigzagPos cu 2 rank t < 2 * lDim) :
    fw_all2all_moe_gmm
        (fw_maybe_shuffle_collective [x0, x1] cu 2 rank)
        (fw_maybe_shuffle_collective [rp0, rp1] cu 2 rank)
        (fw_maybe_shuffle_collective [rm0, rm1] cu 2 rank)
        w13 w2 numExp 0 numExp topK swigluLimit
      = fw_maybe_shuffle_collective
          [fw_all2all_moe_gmm x0 rp0 rm0 w13 w2 numExp 0 numExp topK swigluLimit,
           fw_all2all_moe_gmm x1 rp1 rm1 w13 w2 numExp 0 numExp topK swigluLimit]
          cu 2 rank :=
  row3Local_shuffle_collective_cp2
    (fun x y z => fw_all2all_moe_gmm x y z w13 w2 numExp 0 numExp topK
      swigluLimit)
    hModel numExp hModel lDim rank cu hhModel hnE hhModel hl hrank
    (Row3LocalShape_moe_gmm hModel numExp topK w13 w2 swigluLimit)
    (Row3LocalCongr_moe_gmm hModel numExp topK E_total t_dim d_dim w13 w2
      swigluLimit hhModel ht_even hw13_shape)
    x0 x1 rp0 rp1 rm0 rm1 hx0 hx1 hrp0 hrp1 hrm0 hrm1 hpos

/-- The corresponding all-gather commute (the collective-free direction). -/
theorem fw_all2all_moe_gmm_allGather0_commute_2
    (x0 x1 rp0 rp1 rm0 rm1 w13 w2 : Tensor)
    (lDim hModel numExp topK E_total t_dim d_dim : Nat)
    (swigluLimit : Scalar)
    (hl : 0 < lDim) (hhModel : 0 < hModel) (hnE : 0 < numExp)
    (ht_even : t_dim = 2 * d_dim)
    (hw13_shape : w13.shape = [E_total, t_dim, hModel])
    (hx0 : x0.shape = [lDim, hModel]) (hx1 : x1.shape = [lDim, hModel])
    (hrp0 : rp0.shape = [lDim, numExp]) (hrp1 : rp1.shape = [lDim, numExp])
    (hrm0 : rm0.shape = [lDim, numExp]) (hrm1 : rm1.shape = [lDim, numExp]) :
    fw_all2all_moe_gmm
        (allGatherPrimDimN 0 2 0 [x0, x1])
        (allGatherPrimDimN 0 2 0 [rp0, rp1])
        (allGatherPrimDimN 0 2 0 [rm0, rm1])
        w13 w2 numExp 0 numExp topK swigluLimit
      = allGatherPrimDimN 0 2 0
          [fw_all2all_moe_gmm x0 rp0 rm0 w13 w2 numExp 0 numExp topK swigluLimit,
           fw_all2all_moe_gmm x1 rp1 rm1 w13 w2 numExp 0 numExp topK swigluLimit] :=
  row3Local_allGather0_commute_2
    (fun x y z => fw_all2all_moe_gmm x y z w13 w2 numExp 0 numExp topK
      swigluLimit)
    hModel numExp hModel lDim hhModel hnE hhModel hl
    (Row3LocalShape_moe_gmm hModel numExp topK w13 w2 swigluLimit)
    (Row3LocalCongr_moe_gmm hModel numExp topK E_total t_dim d_dim w13 w2
      swigluLimit hhModel ht_even hw13_shape)
    x0 x1 rp0 rp1 rm0 rm1 hx0 hx1 hrp0 hrp1 hrm0 hrm1

/-- Metadata well-formedness propagates through the MoE expert layer. -/
theorem ZigzagCuWF.all2all_moe_gmm_cp2
    (cu : List Nat) (x0 x1 rp0 rp1 rm0 rm1 w13 w2 : Tensor)
    (lDim hModel numExp topK : Nat) (swigluLimit : Scalar)
    (hwf : ZigzagCuWF cu [x0, x1] 2)
    (hx0 : x0.shape = [lDim, hModel]) (hx1 : x1.shape = [lDim, hModel])
    (hrp0 : rp0.shape = [lDim, numExp]) (hrp1 : rp1.shape = [lDim, numExp])
    (hrm0 : rm0.shape = [lDim, numExp]) (hrm1 : rm1.shape = [lDim, numExp]) :
    ZigzagCuWF cu
      [fw_all2all_moe_gmm x0 rp0 rm0 w13 w2 numExp 0 numExp topK swigluLimit,
       fw_all2all_moe_gmm x1 rp1 rm1 w13 w2 numExp 0 numExp topK swigluLimit]
      2 :=
  ZigzagCuWF.row3Local_cp2
    (fun x y z => fw_all2all_moe_gmm x y z w13 w2 numExp 0 numExp topK
      swigluLimit)
    cu x0 x1 rp0 rp1 rm0 rm1 lDim hModel numExp hModel
    (Row3LocalShape_moe_gmm hModel numExp topK w13 w2 swigluLimit)
    hwf hx0 hx1 hrp0 hrp1 hrm0 hrm1

namespace Zigzag2Rel

/-- **Main theorem.** The MoE expert layer `fw_all2all_moe_gmm` (SM node 526,
`numExperts = 64`, `localExpertStart = 0`, `localExpertEnd = 64`, `topK = 8`)
preserves the CP2 zigzag layout relation, provided the token stream and both
routing metadata streams are laid out against the *same* `cu` metadata. -/
theorem all2all_moe_gmm
    {fx frp frm zx0 zx1 zrp0 zrp1 zrm0 zrm1 cu : Tensor} (w13 w2 : Tensor)
    (lDim hModel numExp topK E_total t_dim d_dim : Nat) (swigluLimit : Scalar)
    (hrelX : Zigzag2Rel fx zx0 zx1 cu [lDim * 2, hModel] [lDim, hModel])
    (hrelRP : Zigzag2Rel frp zrp0 zrp1 cu [lDim * 2, numExp] [lDim, numExp])
    (hrelRM : Zigzag2Rel frm zrm0 zrm1 cu [lDim * 2, numExp] [lDim, numExp])
    (hl : 0 < lDim) (heven : lDim % 2 = 0)
    (hhModel : 0 < hModel) (hnE : 0 < numExp)
    (ht_even : t_dim = 2 * d_dim)
    (hw13_shape : w13.shape = [E_total, t_dim, hModel])
    (hdec : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Zigzag2Rel
      (fw_all2all_moe_gmm fx frp frm w13 w2 numExp 0 numExp topK swigluLimit)
      (fw_all2all_moe_gmm zx0 zrp0 zrm0 w13 w2 numExp 0 numExp topK swigluLimit)
      (fw_all2all_moe_gmm zx1 zrp1 zrm1 w13 w2 numExp 0 numExp topK swigluLimit)
      cu [lDim * 2, hModel] [lDim, hModel] :=
  Zigzag2Rel.row3Local
    (fun x y z => fw_all2all_moe_gmm x y z w13 w2 numExp 0 numExp topK
      swigluLimit)
    hModel numExp hModel lDim hhModel hnE hhModel hl heven
    (Row3LocalShape_moe_gmm hModel numExp topK w13 w2 swigluLimit)
    (Row3LocalCongr_moe_gmm hModel numExp topK E_total t_dim d_dim w13 w2
      swigluLimit hhModel ht_even hw13_shape)
    hrelX hrelRP hrelRM hdec

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
