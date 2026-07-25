/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagLayoutRel

/-!
# The MoE router operators preserve the CP2 zigzag layout relation

The generated graph routes the MoE gate through two nodes:

* SM node 518 `FW_norm_linear ins [5357, 5358] outs [5359]`, i.e.
  `fw_norm_linear x w` with `x : [4096, 1024]` and a *replicated* weight
  `w : [numExperts, 1024]`, producing the logits `[4096, numExperts]`;
* SM node 522 `FW_topk_routing ins [5359] outs [5360, 5361, 5362]
  params [8, 1]`, i.e. `fw_topk_routing logits top_k numExperts`, whose three
  outputs `(routing_probs, routing_map, gate_scores)` all have shape
  `[4096, numExperts]`.

## Row locality audit

Both operators are **row local** (output row `i` reads input row `i` only):

* `fw_norm_linear x w` (`denote/Denote.lean:1789`) computes
  `out[i, n] = Σ_c x[i, c] · normLinearWNormAt w n c k`.  The only `x` reads are
  `valAt x (i * k + c)`; `normLinearWNormAt` reads `w` alone.  Row local.
* `fw_topk_routing logits top_k numExperts` (`denote/Denote.lean:1913`):
  - `gate_scores = softmax logits` and `softmax` (`denote/Denote.lean:504`)
    normalises along the **last** dimension only: `base = batch * d` with
    `batch = flat / d`, so every read stays inside row `batch`.
  - `topkScoresAt g e l x = valAt g (l * e + x)` — row `l` only.
  - `topkRank g e l x` filters `Finset.range e` comparing `topkScoresAt g e l ·`
    values — row `l` only; the tiebreak is the deterministic "lower index wins",
    which is again row local.
  - `inTopK`, `topkScoreSum` are built from those, still row `l` only.
  - Hence all three outputs at `(l, x)` depend on `logits` row `l` only.

  In particular there is **no** cross-token load balancing / auxiliary-loss term
  and **no** cross-token normalisation in the Lean model (matching the pinned
  Python at `llm/arch/all2all_moe.py:85-91`, which is likewise per-row:
  `softmax(dim=-1)`, `topk(k, dim=-1)`, `scores / scores.sum(-1)`).

## Proof structure

Because both operators are row local we factor the argument once, through an
abstract *row-congruence* predicate (`RowLocalCongr`) plus a shape predicate
(`RowLocalShape`), and prove the two required commutations generically:

* with the ordinary dim-0 all-gather (`rowLocal_allGather0_commute_2`);
* with the faithful CP2 shuffle (`rowLocal_shuffle_collective_cp2`).

### Why the shuffle lemma carries a positional hypothesis

`ZigzagLinearRel.lean` could discharge the degenerate `zigzagPos … / lDim ≥ 2`
branch because a linear map sends the all-zero row to the zero row.  That is
*false* for the router: `softmax` of an all-zero row is `1/e`, not `0`.  We
therefore do not fake it — the generic shuffle lemma takes the honest
hypothesis that every local token maps to an in-range global position, and the
`Zigzag2Rel` propagation theorems discharge it from the single-sequence
metadata `decodeCuSeqlens cu = [0, 2 * lDim]` via `zigzagPos_single_lt`.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-! ## Abstract row locality -/

/-- `f` maps `[a, d]`-shaped tensors to `[a, e]`-shaped tensors. -/
def RowLocalShape (f : Tensor → Tensor) (d e : Nat) : Prop :=
  ∀ (a : Nat) (x : Tensor), x.shape = [a, d] → (f x).shape = [a, e]

/-- Output row `ix` of `f x` is determined by input row `ix` of `x`: if two
(possibly differently sized) inputs agree on one whole row, the outputs agree on
the corresponding output row. -/
def RowLocalCongr (f : Tensor → Tensor) (d e : Nat) : Prop :=
  ∀ (a b : Nat) (x y : Tensor) (ix iy c : Nat),
    x.shape = [a, d] → y.shape = [b, d] → ix < a → iy < b → c < e →
    (∀ j, j < d → valAt x (ix * d + j) = valAt y (iy * d + j)) →
    valAt (f x) (ix * e + c) = valAt (f y) (iy * e + c)

theorem lt_two_cases (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by omega

theorem prodShape_2d' (a b : Nat) : prodShape [a, b] = a * b := by
  simp only [prodShape, List.foldl, Nat.one_mul]

/-! ## Row-local operators commute with the CP2 dim-0 all-gather -/

theorem rowLocal_allGather0_commute_2
    (f : Tensor → Tensor) (d e lDim : Nat)
    (hd : 0 < d) (he : 0 < e) (hl : 0 < lDim)
    (hshape : RowLocalShape f d e) (hcongr : RowLocalCongr f d e)
    (a0 a1 : Tensor)
    (ha0 : a0.shape = [lDim, d]) (ha1 : a1.shape = [lDim, d]) :
    f (allGatherPrimDimN 0 2 0 [a0, a1]) =
      allGatherPrimDimN 0 2 0 [f a0, f a1] := by
  have hheadA : (([a0, a1].head?.map (fun t => t.shape)).getD []) = [lDim, d] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, ha0]
  have hF0 : (f a0).shape = [lDim, e] := hshape lDim a0 ha0
  have hF1 : (f a1).shape = [lDim, e] := hshape lDim a1 ha1
  have hheadF : (([f a0, f a1].head?.map (fun t => t.shape)).getD []) =
      [lDim, e] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hF0]
  have hgetA : ∀ r (_ : r < 2),
      ([a0, a1].getD r (zeroTensor [lDim, d])).shape = [lDim, d] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using ha0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using ha1
  have hgetF : ∀ r (_ : r < 2),
      ([f a0, f a1].getD r (zeroTensor [lDim, e])).shape = [lDim, e] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hF0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hF1
  have hG : (allGatherPrimDimN 0 2 0 [a0, a1]).shape = [lDim * 2, d] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, d] hheadA]
    simp only [List.set, List.getD_cons_zero]
  have hGF : (allGatherPrimDimN 0 2 0 [f a0, f a1]).shape = [lDim * 2, e] := by
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, e] hheadF]
    simp only [List.set, List.getD_cons_zero]
  have hlhs : (f (allGatherPrimDimN 0 2 0 [a0, a1])).shape = [lDim * 2, e] :=
    hshape (lDim * 2) _ hG
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
    have hgetAshape : ([a0, a1].getD r (zeroTensor [lDim, d])).shape =
        [lDim, d] := hgetA r hr
    have hrowVals : ∀ j, j < d →
        valAt (allGatherPrimDimN 0 2 0 [a0, a1]) (row * d + j) =
          valAt ([a0, a1].getD r (zeroTensor [lDim, d])) (i * d + j) := by
      intro j hj
      rw [hrowEq]
      exact allGatherPrimDimN0_valAt 2 lDim d [a0, a1] (by decide) hl hd
        hheadA hgetA r hr i hi j hj
    rw [hidxEq]
    rw [hcongr (lDim * 2) lDim (allGatherPrimDimN 0 2 0 [a0, a1])
      ([a0, a1].getD r (zeroTensor [lDim, d])) row i c hG hgetAshape hrow hi hc
      hrowVals]
    rw [hrowEq]
    rw [allGatherPrimDimN0_valAt 2 lDim e [f a0, f a1] (by decide) hl he
      hheadF hgetF r hr i hi c hc]
    interval_cases r
    · simp only [List.getD_cons_zero]
    · simp only [List.getD_cons_succ, List.getD_cons_zero]

/-! ## Row-local operators commute with the faithful CP2 shuffle -/

theorem rowLocal_shuffle_collective_cp2
    (f : Tensor → Tensor) (d e lDim rank : Nat) (cu : List Nat)
    (hd : 0 < d) (he : 0 < e) (hl : 0 < lDim) (hrank : rank < 2)
    (hshape : RowLocalShape f d e) (hcongr : RowLocalCongr f d e)
    (s0 s1 : Tensor)
    (hs0 : s0.shape = [lDim, d]) (hs1 : s1.shape = [lDim, d])
    (hpos : ∀ t, t < lDim → zigzagPos cu 2 rank t < 2 * lDim) :
    f (fw_maybe_shuffle_collective [s0, s1] cu 2 rank) =
      fw_maybe_shuffle_collective [f s0, f s1] cu 2 rank := by
  have hF0 : (f s0).shape = [lDim, e] := hshape lDim s0 hs0
  have hF1 : (f s1).shape = [lDim, e] := hshape lDim s1 hs1
  have hlocal : ([s0, s1].getD rank (zeroTensor [])).shape = [lDim, d] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hs0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
  have hlocalF : ([f s0, f s1].getD rank (zeroTensor [])).shape =
      [lDim, e] := by
    interval_cases rank
    · simpa only [List.getD_cons_zero] using hF0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hF1
  have hshuffleShape :
      (fw_maybe_shuffle_collective [s0, s1] cu 2 rank).shape = [lDim, d] := by
    rw [fw_maybe_shuffle_collective_shape]; exact hlocal
  have hlhs : (f (fw_maybe_shuffle_collective [s0, s1] cu 2 rank)).shape =
      [lDim, e] := hshape lDim _ hshuffleShape
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
    set g := zigzagPos cu 2 rank row with hgdef
    have hglt : g < 2 * lDim := hpos row hrow
    have hi : g % lDim < lDim := Nat.mod_lt _ hl
    have hr : g / lDim < 2 := by
      refine (Nat.div_lt_iff_lt_mul hl).mpr ?_
      omega
    have hgetShape : ([s0, s1].getD (g / lDim) (zeroTensor [])).shape =
        [lDim, d] := by
      have h2 : g / lDim = 0 ∨ g / lDim = 1 := lt_two_cases _ hr
      rcases h2 with h | h
      · rw [h]; simpa only [List.getD_cons_zero] using hs0
      · rw [h]; simpa only [List.getD_cons_succ, List.getD_cons_zero] using hs1
    -- reading a shuffled input row is reading one source row
    have hinput : ∀ j, j < d →
        valAt (fw_maybe_shuffle_collective [s0, s1] cu 2 rank) (row * d + j) =
          valAt ([s0, s1].getD (g / lDim) (zeroTensor []))
            (g % lDim * d + j) := by
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
      rfl
    rw [hidxEq]
    rw [hcongr lDim lDim (fw_maybe_shuffle_collective [s0, s1] cu 2 rank)
      ([s0, s1].getD (g / lDim) (zeroTensor [])) row (g % lDim) c
      hshuffleShape hgetShape hrow hi hc hinput]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by decide)
      (by rw [hlocalF, prodShape_2d']
          calc row * e + c < row * e + e := Nat.add_lt_add_left hc _
            _ = (row + 1) * e := by ring
            _ ≤ lDim * e := Nat.mul_le_mul_right _ hrow)]
    simp only [hlocalF, List.tail_cons, prodShape, List.foldl,
      Nat.one_mul, List.getD_cons_zero]
    rw [show row * e + c = c + e * row by ring,
      Nat.add_mul_div_left _ _ he, Nat.div_eq_of_lt hc, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    unfold gatherFromRank
    rw [← hgdef]
    have h2 : g / lDim = 0 ∨ g / lDim = 1 := lt_two_cases _ hr
    rcases h2 with h | h
    · rw [h]; simp only [List.getD_cons_zero]
    · rw [h]; simp only [List.getD_cons_succ, List.getD_cons_zero]

/-! ## The zigzag position of an in-range token is in range (single sequence) -/

/-- For one packed sequence of `2 * lDim` tokens split across CP2, every local
token maps to a global position inside `[0, 2 * lDim)`. -/
theorem zigzagPos_single_lt (lDim rank k : Nat)
    (heven : lDim % 2 = 0) (hrank : rank < 2) (hk : k < lDim) :
    zigzagPos [0, 2 * lDim] 2 rank k < 2 * lDim := by
  obtain ⟨m, rfl⟩ : ∃ m, lDim = 2 * m := ⟨lDim / 2, by omega⟩
  have hsl : sliceSizeAt [0, 2 * (2 * m)] 4 0 = m := by
    show (List.getD [0, 2 * (2 * m)] 1 0 - List.getD [0, 2 * (2 * m)] 0 0) / 4 = m
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.sub_zero]
    omega
  have hunfold : zigzagPosAux [0, 2 * (2 * m)] 4 rank k 0 1 =
      (if k < m then 0 + rank * m + k
       else if k < 2 * m then 0 + (4 - rank - 1) * m + (k - m)
       else 0) := by
    show (let sl := sliceSizeAt [0, 2 * (2 * m)] 4 0
          let seqStart := List.getD [0, 2 * (2 * m)] 0 0
          if k < sl then seqStart + rank * sl + k
          else if k < 2 * sl then seqStart + (4 - rank - 1) * sl + (k - sl)
          else zigzagPosAux [0, 2 * (2 * m)] 4 rank (k - 2 * sl) (0 + 1) 0) = _
    rw [hsl]
    show (if k < m then List.getD [0, 2 * (2 * m)] 0 0 + rank * m + k
          else if k < 2 * m then
            List.getD [0, 2 * (2 * m)] 0 0 + (4 - rank - 1) * m + (k - m)
          else zigzagPosAux [0, 2 * (2 * m)] 4 rank (k - 2 * m) (0 + 1) 0) = _
    simp only [List.getD_cons_zero]
    split_ifs <;> rfl
  show zigzagPosAux [0, 2 * (2 * m)] 4 rank k 0 1 < 2 * (2 * m)
  rw [hunfold]
  interval_cases rank <;> split_ifs <;> omega

/-! ## Metadata well-formedness transports along a row-local operator -/

theorem ZigzagCuWF.rowLocal_cp2
    (f : Tensor → Tensor) (cu : List Nat) (s0 s1 : Tensor) (lDim d e : Nat)
    (hshape : RowLocalShape f d e)
    (hwf : ZigzagCuWF cu [s0, s1] 2)
    (hs0 : s0.shape = [lDim, d]) (hs1 : s1.shape = [lDim, d]) :
    ZigzagCuWF cu [f s0, f s1] 2 := by
  have hF0 : (f s0).shape = [lDim, e] := hshape lDim s0 hs0
  have hF1 : (f s1).shape = [lDim, e] := hshape lDim s1 hs1
  refine ⟨hwf.cp_pos, rfl, hwf.cu_starts_zero, hwf.cu_has_endpoint,
    hwf.monotone, hwf.divisible, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hF0]; exact List.cons_ne_nil _ _
    · rw [hF1]; exact List.cons_ne_nil _ _
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rfl
    · simp only [List.getD_cons_zero]
      rw [hF1, hF0]
  · have h := hwf.local_tokens
    simp only [List.getD_cons_zero, hs0] at h
    simpa only [List.getD_cons_zero, hF0] using h

namespace Zigzag2Rel

/-- **Master propagation lemma.** Any row-local operator `[a, d] → [a, e]`
preserves the CP2 zigzag layout relation, for single-sequence packed metadata.
-/
theorem rowLocal
    {full z0 z1 cu : Tensor} (f : Tensor → Tensor) (d e lDim : Nat)
    (hd : 0 < d) (he : 0 < e) (hl : 0 < lDim) (heven : lDim % 2 = 0)
    (hshape : RowLocalShape f d e) (hcongr : RowLocalCongr f d e)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, d] [lDim, d])
    (hdec : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Zigzag2Rel (f full) (f z0) (f z1) cu [lDim * 2, e] [lDim, e] := by
  rcases hrel with ⟨s0, s1, hs⟩
  have hs0 : s0.shape = [lDim, d] := hs.source0_shape
  have hs1 : s1.shape = [lDim, d] := hs.source1_shape
  have hpos : ∀ rank, rank < 2 → ∀ t, t < lDim →
      zigzagPos (decodeCuSeqlens cu) 2 rank t < 2 * lDim := by
    intro rank hrank t ht
    rw [hdec]
    exact zigzagPos_single_lt lDim rank t heven hrank ht
  refine ⟨f s0, f s1, ?_, ?_, ?_, ?_,
    hshape lDim s0 hs0, hshape lDim s1 hs1, ?_, ?_,
    ZigzagCuWF.rowLocal_cp2 f _ s0 s1 lDim d e hshape hs.cu_wf hs0 hs1⟩
  · rw [hs.full_value]
    exact rowLocal_allGather0_commute_2 f d e lDim hd he hl hshape hcongr
      s0 s1 hs0 hs1
  · rw [hs.rank0_value]
    exact rowLocal_shuffle_collective_cp2 f d e lDim 0 (decodeCuSeqlens cu)
      hd he hl (by decide) hshape hcongr s0 s1 hs0 hs1 (hpos 0 (by decide))
  · rw [hs.rank1_value]
    exact rowLocal_shuffle_collective_cp2 f d e lDim 1 (decodeCuSeqlens cu)
      hd he hl (by decide) hshape hcongr s0 s1 hs0 hs1 (hpos 1 (by decide))
  · exact hshape (lDim * 2) full hs.full_shape
  · exact hshape lDim z0 hs.rank0_shape
  · exact hshape lDim z1 hs.rank1_shape

end Zigzag2Rel

/-! ## Instance 1: `fw_norm_linear` with a replicated weight -/

/-- Reduced form of `fw_norm_linear` in the 2-D weight branch. -/
theorem fw_norm_linear_is_2d (b k n : Nat) (x w : Tensor) (hn : 0 < n)
    (hx : x.shape = [b, k]) (hw : w.shape = [n, k]) :
    fw_norm_linear x w = Tensor.mkShape [b, n]
      (fun outIdx => ∑ c ∈ Finset.range k,
        valAt x ((outIdx.1 / n) * k + c) *
          normLinearWNormAt w (outIdx.1 % n) c k) := by
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  unfold fw_norm_linear
  rw [hx, hw]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, if_neg hn']
  rfl

theorem fw_norm_linear_shape_2d (b k n : Nat) (x w : Tensor) (hn : 0 < n)
    (hx : x.shape = [b, k]) (hw : w.shape = [n, k]) :
    (fw_norm_linear x w).shape = [b, n] := by
  rw [fw_norm_linear_is_2d b k n x w hn hx hw]; rfl

theorem fw_norm_linear_valAt_2d (b k n : Nat) (x w : Tensor) (hn : 0 < n)
    (hx : x.shape = [b, k]) (hw : w.shape = [n, k])
    (i c : Nat) (hi : i < b) (hc : c < n) :
    valAt (fw_norm_linear x w) (i * n + c) =
      ∑ j ∈ Finset.range k, valAt x (i * k + j) * normLinearWNormAt w c j k := by
  have hbound : i * n + c < prodShape [b, n] := by
    rw [prodShape_2d']
    calc i * n + c < i * n + n := Nat.add_lt_add_left hc _
      _ = (i + 1) * n := by ring
      _ ≤ b * n := Nat.mul_le_mul_right _ hi
  rw [fw_norm_linear_is_2d b k n x w hn hx hw]
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hbound)]
  have hdiv : (i * n + c) / n = i := by
    rw [show i * n + c = c + n * i by ring,
      Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (i * n + c) % n = c := by
    rw [show i * n + c = c + n * i by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  show (∑ j ∈ Finset.range k,
      valAt x ((i * n + c) / n * k + j) *
        normLinearWNormAt w ((i * n + c) % n) j k) = _
  rw [hdiv, hmod]

theorem RowLocalShape_norm_linear (k n : Nat) (w : Tensor) (hn : 0 < n)
    (hw : w.shape = [n, k]) : RowLocalShape (fun x => fw_norm_linear x w) k n :=
  fun a x hx => fw_norm_linear_shape_2d a k n x w hn hx hw

theorem RowLocalCongr_norm_linear (k n : Nat) (w : Tensor) (hn : 0 < n)
    (hw : w.shape = [n, k]) : RowLocalCongr (fun x => fw_norm_linear x w) k n := by
  intro a b x y ix iy c hx hy hix hiy hc hrow
  rw [fw_norm_linear_valAt_2d a k n x w hn hx hw ix c hix hc]
  rw [fw_norm_linear_valAt_2d b k n y w hn hy hw iy c hiy hc]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [hrow j (Finset.mem_range.mp hj)]

namespace Zigzag2Rel

/-- `FW_norm_linear` (SM node 518) with a **replicated** weight `w : [n, k]`
preserves the CP2 zigzag layout relation. -/
theorem norm_linear
    {full z0 z1 cu w : Tensor} (lDim k n : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, k] [lDim, k])
    (hw : w.shape = [n, k])
    (hl : 0 < lDim) (heven : lDim % 2 = 0) (hk : 0 < k) (hn : 0 < n)
    (hdec : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Zigzag2Rel (fw_norm_linear full w) (fw_norm_linear z0 w)
      (fw_norm_linear z1 w) cu [lDim * 2, n] [lDim, n] :=
  Zigzag2Rel.rowLocal (fun x => fw_norm_linear x w) k n lDim hk hn hl heven
    (RowLocalShape_norm_linear k n w hn hw)
    (RowLocalCongr_norm_linear k n w hn hw) hrel hdec

end Zigzag2Rel

/-! ## Instance 2: `fw_topk_routing` (all three outputs) -/

/-- Reduced form of `softmax` on a 2-D tensor. -/
theorem softmax_is_2d (a d : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) :
    softmax x = Tensor.mkShape [a, d] (fun outIdx =>
      let expSum := ∑ j ∈ Finset.range d,
        expFn (valAt x (outIdx.1 / d * d + j))
      if expSum = 0 then 0
      else expFn (valAt x (outIdx.1 / d * d + outIdx.1 % d)) / expSum) := by
  have hd' : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  unfold softmax
  rw [hx]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, if_neg hd']

theorem softmax_valAt_2d (a d : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) (i c : Nat) (hi : i < a) (hc : c < d) :
    valAt (softmax x) (i * d + c) =
      (let expSum := ∑ j ∈ Finset.range d, expFn (valAt x (i * d + j))
       if expSum = 0 then 0 else expFn (valAt x (i * d + c)) / expSum) := by
  have hbound : i * d + c < prodShape [a, d] := by
    rw [prodShape_2d']
    calc i * d + c < i * d + d := Nat.add_lt_add_left hc _
      _ = (i + 1) * d := by ring
      _ ≤ a * d := Nat.mul_le_mul_right _ hi
  rw [softmax_is_2d a d x hd hx]
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hbound)]
  have hdiv : (i * d + c) / d = i := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (i * d + c) % d = c := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  show (let expSum := ∑ j ∈ Finset.range d,
          expFn (valAt x ((i * d + c) / d * d + j))
        if expSum = 0 then 0
        else expFn (valAt x ((i * d + c) / d * d + (i * d + c) % d)) /
          expSum) = _
  rw [hdiv, hmod]

/-- `softmax` is row local: agreeing rows give agreeing softmax rows. -/
theorem softmax_row_congr (a b d : Nat) (x y : Tensor) (ix iy : Nat)
    (hd : 0 < d) (hx : x.shape = [a, d]) (hy : y.shape = [b, d])
    (hix : ix < a) (hiy : iy < b)
    (hrow : ∀ j, j < d → valAt x (ix * d + j) = valAt y (iy * d + j)) :
    ∀ c, c < d → valAt (softmax x) (ix * d + c) = valAt (softmax y) (iy * d + c) := by
  intro c hc
  rw [softmax_valAt_2d a d x hd hx ix c hix hc]
  rw [softmax_valAt_2d b d y hd hy iy c hiy hc]
  have hsum : (∑ j ∈ Finset.range d, expFn (valAt x (ix * d + j))) =
      ∑ j ∈ Finset.range d, expFn (valAt y (iy * d + j)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hrow j (Finset.mem_range.mp hj)]
  show (if _ = 0 then _ else _) = _
  rw [hsum, hrow c hc]

/-- The whole top-k row machinery only reads one row of `gate_scores`. -/
theorem topk_row_machinery_congr (d top_k : Nat) (g h : Tensor) (l l' : Nat)
    (hrow : ∀ c, c < d → topkScoresAt g d l c = topkScoresAt h d l' c) :
    (∀ c, c < d → topkRank g d l c = topkRank h d l' c) ∧
      (∀ c, c < d → inTopK g d top_k l c = inTopK h d top_k l' c) ∧
      topkScoreSum g d top_k l = topkScoreSum h d top_k l' := by
  have hrank : ∀ c, c < d → topkRank g d l c = topkRank h d l' c := by
    intro c hc
    unfold topkRank
    congr 1
    refine Finset.filter_congr ?_
    intro e' he'
    rw [hrow e' (Finset.mem_range.mp he'), hrow c hc]
  have htop : ∀ c, c < d → inTopK g d top_k l c = inTopK h d top_k l' c := by
    intro c hc
    unfold inTopK
    rw [hrank c hc]
  refine ⟨hrank, htop, ?_⟩
  unfold topkScoreSum
  refine Finset.sum_congr rfl ?_
  intro e' he'
  have he'd := Finset.mem_range.mp he'
  rw [htop e' he'd, hrow e' he'd]

/-- Reduced form of the first output (`routing_probs`) of `fw_topk_routing`. -/
theorem fw_topk_routing_fst_eq (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) :
    (fw_topk_routing x top_k d).1 = Tensor.mkShape [a, d] (fun outIdx =>
      if inTopK (softmax x) d top_k (outIdx.1 / d) (outIdx.1 % d) then
        (if topkScoreSum (softmax x) d top_k (outIdx.1 / d) = 0 then 0
         else topkScoresAt (softmax x) d (outIdx.1 / d) (outIdx.1 % d) /
           topkScoreSum (softmax x) d top_k (outIdx.1 / d))
      else 0) := by
  have hd' : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  unfold fw_topk_routing
  rw [hx]
  simp only [List.head?_cons, Option.getD_some, if_neg hd']

/-- Reduced form of the second output (`routing_map`) of `fw_topk_routing`. -/
theorem fw_topk_routing_snd_eq (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) :
    (fw_topk_routing x top_k d).2.1 = Tensor.mkShape [a, d] (fun outIdx =>
      if inTopK (softmax x) d top_k (outIdx.1 / d) (outIdx.1 % d) then 1
      else 0) := by
  have hd' : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  unfold fw_topk_routing
  rw [hx]
  simp only [List.head?_cons, Option.getD_some, if_neg hd']

/-- Third output of `fw_topk_routing` is exactly `softmax`. -/
theorem fw_topk_routing_thd_eq (top_k d : Nat) (x : Tensor) :
    (fw_topk_routing x top_k d).2.2 = softmax x := rfl

theorem fw_topk_routing_fst_shape (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) : (fw_topk_routing x top_k d).1.shape = [a, d] := by
  rw [fw_topk_routing_fst_eq a d top_k x hd hx]; rfl

theorem fw_topk_routing_snd_shape (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) : (fw_topk_routing x top_k d).2.1.shape = [a, d] := by
  rw [fw_topk_routing_snd_eq a d top_k x hd hx]; rfl

theorem fw_topk_routing_fst_valAt (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) (i c : Nat) (hi : i < a) (hc : c < d) :
    valAt (fw_topk_routing x top_k d).1 (i * d + c) =
      (if inTopK (softmax x) d top_k i c then
        (if topkScoreSum (softmax x) d top_k i = 0 then 0
         else topkScoresAt (softmax x) d i c /
           topkScoreSum (softmax x) d top_k i)
      else 0) := by
  have hbound : i * d + c < prodShape [a, d] := by
    rw [prodShape_2d']
    calc i * d + c < i * d + d := Nat.add_lt_add_left hc _
      _ = (i + 1) * d := by ring
      _ ≤ a * d := Nat.mul_le_mul_right _ hi
  have hdiv : (i * d + c) / d = i := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (i * d + c) % d = c := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  rw [fw_topk_routing_fst_eq a d top_k x hd hx]
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hbound)]
  show (if inTopK (softmax x) d top_k ((i * d + c) / d) ((i * d + c) % d) then
      (if topkScoreSum (softmax x) d top_k ((i * d + c) / d) = 0 then 0
       else topkScoresAt (softmax x) d ((i * d + c) / d) ((i * d + c) % d) /
         topkScoreSum (softmax x) d top_k ((i * d + c) / d))
    else 0) = _
  rw [hdiv, hmod]

theorem fw_topk_routing_snd_valAt (a d top_k : Nat) (x : Tensor) (hd : 0 < d)
    (hx : x.shape = [a, d]) (i c : Nat) (hi : i < a) (hc : c < d) :
    valAt (fw_topk_routing x top_k d).2.1 (i * d + c) =
      (if inTopK (softmax x) d top_k i c then 1 else 0) := by
  have hbound : i * d + c < prodShape [a, d] := by
    rw [prodShape_2d']
    calc i * d + c < i * d + d := Nat.add_lt_add_left hc _
      _ = (i + 1) * d := by ring
      _ ≤ a * d := Nat.mul_le_mul_right _ hi
  have hdiv : (i * d + c) / d = i := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (i * d + c) % d = c := by
    rw [show i * d + c = c + d * i by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  rw [fw_topk_routing_snd_eq a d top_k x hd hx]
  rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hbound)]
  show (if inTopK (softmax x) d top_k ((i * d + c) / d) ((i * d + c) % d) then
      (1 : Scalar) else 0) = _
  rw [hdiv, hmod]

/-- Common row-congruence core for the two derived `fw_topk_routing` outputs. -/
theorem topk_scores_row_congr (a b d : Nat) (x y : Tensor) (ix iy : Nat)
    (hd : 0 < d) (hx : x.shape = [a, d]) (hy : y.shape = [b, d])
    (hix : ix < a) (hiy : iy < b)
    (hrow : ∀ j, j < d → valAt x (ix * d + j) = valAt y (iy * d + j)) :
    ∀ c, c < d →
      topkScoresAt (softmax x) d ix c = topkScoresAt (softmax y) d iy c := by
  intro c hc
  unfold topkScoresAt
  exact softmax_row_congr a b d x y ix iy hd hx hy hix hiy hrow c hc

theorem RowLocalShape_topk_fst (d top_k : Nat) (hd : 0 < d) :
    RowLocalShape (fun x => (fw_topk_routing x top_k d).1) d d :=
  fun a x hx => fw_topk_routing_fst_shape a d top_k x hd hx

theorem RowLocalShape_topk_snd (d top_k : Nat) (hd : 0 < d) :
    RowLocalShape (fun x => (fw_topk_routing x top_k d).2.1) d d :=
  fun a x hx => fw_topk_routing_snd_shape a d top_k x hd hx

theorem RowLocalShape_topk_thd (d top_k : Nat) :
    RowLocalShape (fun x => (fw_topk_routing x top_k d).2.2) d d := by
  intro a x hx
  show (fw_topk_routing x top_k d).2.2.shape = [a, d]
  rw [fw_topk_routing_thd_eq, softmax_shape_g18, hx]

theorem RowLocalCongr_topk_fst (d top_k : Nat) (hd : 0 < d) :
    RowLocalCongr (fun x => (fw_topk_routing x top_k d).1) d d := by
  intro a b x y ix iy c hx hy hix hiy hc hrow
  have hsc := topk_scores_row_congr a b d x y ix iy hd hx hy hix hiy hrow
  obtain ⟨_, htop, hsum⟩ :=
    topk_row_machinery_congr d top_k (softmax x) (softmax y) ix iy hsc
  rw [fw_topk_routing_fst_valAt a d top_k x hd hx ix c hix hc]
  rw [fw_topk_routing_fst_valAt b d top_k y hd hy iy c hiy hc]
  rw [htop c hc, hsum, hsc c hc]

theorem RowLocalCongr_topk_snd (d top_k : Nat) (hd : 0 < d) :
    RowLocalCongr (fun x => (fw_topk_routing x top_k d).2.1) d d := by
  intro a b x y ix iy c hx hy hix hiy hc hrow
  have hsc := topk_scores_row_congr a b d x y ix iy hd hx hy hix hiy hrow
  obtain ⟨_, htop, _⟩ :=
    topk_row_machinery_congr d top_k (softmax x) (softmax y) ix iy hsc
  rw [fw_topk_routing_snd_valAt a d top_k x hd hx ix c hix hc]
  rw [fw_topk_routing_snd_valAt b d top_k y hd hy iy c hiy hc]
  rw [htop c hc]

theorem RowLocalCongr_topk_thd (d top_k : Nat) (hd : 0 < d) :
    RowLocalCongr (fun x => (fw_topk_routing x top_k d).2.2) d d := by
  intro a b x y ix iy c hx hy hix hiy hc hrow
  show valAt (fw_topk_routing x top_k d).2.2 (ix * d + c) =
    valAt (fw_topk_routing y top_k d).2.2 (iy * d + c)
  rw [fw_topk_routing_thd_eq, fw_topk_routing_thd_eq]
  exact softmax_row_congr a b d x y ix iy hd hx hy hix hiy hrow c hc

namespace Zigzag2Rel

/-- `FW_topk_routing` first output (`routing_probs`) preserves the layout. -/
theorem topk_routing_probs
    {full z0 z1 cu : Tensor} (lDim numExperts top_k : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, numExperts] [lDim, numExperts])
    (hl : 0 < lDim) (heven : lDim % 2 = 0) (he : 0 < numExperts)
    (hdec : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Zigzag2Rel (fw_topk_routing full top_k numExperts).1
      (fw_topk_routing z0 top_k numExperts).1
      (fw_topk_routing z1 top_k numExperts).1
      cu [lDim * 2, numExperts] [lDim, numExperts] :=
  Zigzag2Rel.rowLocal (fun x => (fw_topk_routing x top_k numExperts).1)
    numExperts numExperts lDim he he hl heven
    (RowLocalShape_topk_fst numExperts top_k he)
    (RowLocalCongr_topk_fst numExperts top_k he) hrel hdec

/-- `FW_topk_routing` second output (`routing_map`) preserves the layout. -/
theorem topk_routing_map
    {full z0 z1 cu : Tensor} (lDim numExperts top_k : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, numExperts] [lDim, numExperts])
    (hl : 0 < lDim) (heven : lDim % 2 = 0) (he : 0 < numExperts)
    (hdec : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Zigzag2Rel (fw_topk_routing full top_k numExperts).2.1
      (fw_topk_routing z0 top_k numExperts).2.1
      (fw_topk_routing z1 top_k numExperts).2.1
      cu [lDim * 2, numExperts] [lDim, numExperts] :=
  Zigzag2Rel.rowLocal (fun x => (fw_topk_routing x top_k numExperts).2.1)
    numExperts numExperts lDim he he hl heven
    (RowLocalShape_topk_snd numExperts top_k he)
    (RowLocalCongr_topk_snd numExperts top_k he) hrel hdec

/-- `FW_topk_routing` third output (`gate_scores`) preserves the layout. -/
theorem topk_routing_gate_scores
    {full z0 z1 cu : Tensor} (lDim numExperts top_k : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, numExperts] [lDim, numExperts])
    (hl : 0 < lDim) (heven : lDim % 2 = 0) (he : 0 < numExperts)
    (hdec : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Zigzag2Rel (fw_topk_routing full top_k numExperts).2.2
      (fw_topk_routing z0 top_k numExperts).2.2
      (fw_topk_routing z1 top_k numExperts).2.2
      cu [lDim * 2, numExperts] [lDim, numExperts] :=
  Zigzag2Rel.rowLocal (fun x => (fw_topk_routing x top_k numExperts).2.2)
    numExperts numExperts lDim he he hl heven
    (RowLocalShape_topk_thd numExperts top_k)
    (RowLocalCongr_topk_thd numExperts top_k he) hrel hdec

/-- All three `FW_topk_routing` outputs at once (SM node 522). -/
theorem topk_routing_all
    {full z0 z1 cu : Tensor} (lDim numExperts top_k : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, numExperts] [lDim, numExperts])
    (hl : 0 < lDim) (heven : lDim % 2 = 0) (he : 0 < numExperts)
    (hdec : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Zigzag2Rel (fw_topk_routing full top_k numExperts).1
        (fw_topk_routing z0 top_k numExperts).1
        (fw_topk_routing z1 top_k numExperts).1
        cu [lDim * 2, numExperts] [lDim, numExperts] ∧
      Zigzag2Rel (fw_topk_routing full top_k numExperts).2.1
        (fw_topk_routing z0 top_k numExperts).2.1
        (fw_topk_routing z1 top_k numExperts).2.1
        cu [lDim * 2, numExperts] [lDim, numExperts] ∧
      Zigzag2Rel (fw_topk_routing full top_k numExperts).2.2
        (fw_topk_routing z0 top_k numExperts).2.2
        (fw_topk_routing z1 top_k numExperts).2.2
        cu [lDim * 2, numExperts] [lDim, numExperts] :=
  ⟨topk_routing_probs lDim numExperts top_k hrel hl heven he hdec,
   topk_routing_map lDim numExperts top_k hrel hl heven he hdec,
   topk_routing_gate_scores lDim numExperts top_k hrel hl heven he hdec⟩

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
