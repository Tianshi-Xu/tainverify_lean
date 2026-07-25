/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagMoEGmmRel

/-!
# MoE expert layer with *expert-range sharding* preserves the CP2 zigzag layout

## Why `Zigzag2Rel.all2all_moe_gmm` does not apply to the real generated graph

`ZigzagMoEGmmRel.lean:665` proves the zigzag propagation for the *symmetric*
configuration in which all three sides run `fw_all2all_moe_gmm … w13 w2 numExp
0 numExp topK` with one **replicated** weight pair.  The actual generated graph
is not of that form:

| side       | `[numExp, start, end, topK]` | weights                                |
|------------|------------------------------|----------------------------------------|
| SM 526     | `[64, 0, 64, 8]`             | full `[64,1024,1024]` / `[64,1024,512]` |
| PM r0 1116 | `[64, 0, 32, 8]`             | `[32,…]` shards                         |
| PM r1 1119 | `[64, 32, 64, 8]`            | `[32,…]` shards                         |

so the two ranks use **different expert ranges** and **different (sharded)**
weights, and the SM side reads the dim-0 all-gather of the two weight shards.

## Paper feasibility (the question that had to be settled first)

The drafted route was to weaken `Row3LocalCongr` into an asymmetric
`row3LocalAsym f_full f_0 f_1`.  That turns out to be unnecessary, because a
*stronger and much cheaper* fact holds:

> **Collapse lemma.**  If a rank's routing map is zero on every expert outside
> its own local range, then that rank's half-range operator on its **local**
> weight shard is *literally the same tensor* as the full-range operator on the
> **gathered** weights.

Concretely (`moe_gmm_lower_collapse` / `moe_gmm_upper_collapse` below): the
full-range sum `∑ eLocal ∈ range (2*E)` splits via `Finset.sum_range_add` into
`∑ x ∈ range E` plus `∑ x ∈ range E` at shifted expert `E + x`.

* For rank 0 the shifted half is exactly the block whose mask index is
  `l * numExp + (E + x)` with `E ≤ E + x < 2*E`; the disjointness hypothesis
  forces `mask = 0`, and `fw_all2all_moe_gmm`'s body is
  `if mask = 0 then 0 else …` — so **every one of those terms is definitionally
  `0`**.  The surviving half reads `gW13` at expert `0*E + x`, which
  `allGatherPrimDimN` sends to `w13_a` at `x`; that is precisely what the local
  half-range operator reads.
* For rank 1 the roles are swapped: the *unshifted* half dies by disjointness,
  and the shifted half reads `gW13` at `1*E + x = E + x`, i.e. `w13_b` at `x`,
  matching the local operator whose `start = E` and whose weight index is the
  bare `eLocal`.

So the congruence condition **does** hold in the `mask = 0` branch, exactly as
conjectured — and it holds in the sharp form "the two tensors are equal", not
merely "they agree row-wise".  Once both ranks are rewritten to the common
operator

  `F := fun x y z => fw_all2all_moe_gmm x y z gW13 gW2 (2*E) 0 (2*E) topK`

the goal is *verbatim* the already-proved `Zigzag2Rel.all2all_moe_gmm`.

## Shape of the disjointness hypotheses

Note carefully that the hypotheses are stated on the **zigzag-exposed** rank
tensors `zrm0` / `zrm1`, not on the hidden ordinary source witnesses.  This is
the honest form: rank `r` runs its expert range against the tokens it actually
holds *after* the CP shuffle, so the routing/expert disjointness that makes
expert-range splitting sound is a statement about the shuffled rows.  Because
the collapse lemma is applied *before* any zigzag reasoning, no transport of
disjointness through `zigzagPos` is required at all.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-! ## Reading a dim-0 all-gather of two 3-D weight shards -/

/-- 3-D variant of `allGatherPrimDimN0_valAt` for shard shape `[E, h, d]`. -/
theorem allGather2_3d_valAt (E h d : Nat) (hE : 0 < E) (hh : 0 < h) (hd : 0 < d)
    (Ws : List Tensor)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [E, h, d])
    (r : Nat) (hr : r < 2) (eLocal : Nat) (heLocal : eLocal < E)
    (hi : Nat) (hi_lt : hi < h) (di : Nat) (hdi_lt : di < d) :
    valAt (allGatherPrimDimN 0 2 0 Ws) (((r * E + eLocal) * h + hi) * d + di)
      = valAt (Ws.getD r (zeroTensor [E, h, d])) ((eLocal * h + hi) * d + di) := by
  unfold allGatherPrimDimN
  rw [hhead]
  simp only [List.drop, List.foldl, List.getD]
  have hout_bound : ((r * E + eLocal) * h + hi) * d + di < E * 2 * h * d := by
    have hstep1 : ((r * E + eLocal) * h + hi) * d + di
        < ((r * E + eLocal) * h + hi + 1) * d := by
      calc ((r * E + eLocal) * h + hi) * d + di
          < ((r * E + eLocal) * h + hi) * d + d := by omega
        _ = ((r * E + eLocal) * h + hi + 1) * d := by ring
    have hstep2 : (r * E + eLocal) * h + hi + 1 ≤ (r * E + eLocal + 1) * h := by
      have : (r * E + eLocal + 1) * h = (r * E + eLocal) * h + h := by ring
      omega
    have hstep3 : (r * E + eLocal + 1) ≤ E * 2 := by
      calc r * E + eLocal + 1 ≤ r * E + E := by omega
        _ = (r + 1) * E := by ring
        _ ≤ 2 * E := Nat.mul_le_mul_right _ (by omega)
        _ = E * 2 := by ring
    calc ((r * E + eLocal) * h + hi) * d + di
        < ((r * E + eLocal) * h + hi + 1) * d := hstep1
      _ ≤ (r * E + eLocal + 1) * h * d := by
        have := Nat.mul_le_mul_right d hstep2
        nlinarith
      _ ≤ E * 2 * h * d := by
        have := Nat.mul_le_mul_right (h * d) hstep3
        nlinarith
  rw [valAt_of_lt _ _ (by
    show ((r * E + eLocal) * h + hi) * d + di
      < prodShape ([E, h, d].set 0 (([E, h, d].getD 0 0) * 2))
    simp [prodShape, List.set, List.getD, List.foldl]
    linarith [hout_bound])]
  simp [Tensor.mkShape, List.set, List.getD, List.drop, List.foldl]
  set idx := ((r * E + eLocal) * h + hi) * d + di with hidx_def
  have hE_ne : E ≠ 0 := Nat.pos_iff_ne_zero.mp hE
  have hh_ne : h ≠ 0 := Nat.pos_iff_ne_zero.mp hh
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have hE2_ne : E * 2 ≠ 0 := Nat.mul_ne_zero hE_ne (by omega)
  have hhd_ne : h * d ≠ 0 := Nat.mul_ne_zero hh_ne hd_ne
  have hEhd_ne : E * 2 * (h * d) ≠ 0 := Nat.mul_ne_zero hE2_ne hhd_ne
  have hidx_bound2 : idx < E * 2 * (h * d) := by
    rw [hidx_def]; simp only [Nat.mul_assoc]; convert hout_bound using 1; ring
  have hpre_div : idx / (E * 2 * (h * d)) = 0 := Nat.div_eq_of_lt hidx_bound2
  have hpre_mod : idx % (E * 2 * (h * d)) = idx := Nat.mod_eq_of_lt hidx_bound2
  have h_small_lt : hi * d + di < h * d := by
    calc hi * d + di < hi * d + d := by omega
      _ = (hi + 1) * d := by ring
      _ ≤ h * d := Nat.mul_le_mul_right _ (by omega)
  have hsplit : idx = (r * E + eLocal) * (h * d) + (hi * d + di) := by
    rw [hidx_def]; ring
  have hjFull_val : idx / (h * d) = r * E + eLocal := by
    rw [hsplit, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt h_small_lt, Nat.zero_add]
  have hk_val : idx % (h * d) = hi * d + di := by
    rw [hsplit, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt h_small_lt]
  have hr'_val : (r * E + eLocal) / E = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right eLocal r hE,
      Nat.div_eq_of_lt heLocal, Nat.zero_add]
  have hjLocal_val : (r * E + eLocal) % E = eLocal := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt heLocal]
  simp [hE_ne, hh_ne, hd_ne, hE2_ne, hhd_ne, hEhd_ne, hpre_div, hpre_mod,
    hjFull_val, hk_val, hr'_val, hjLocal_val]
  ring_nf

/-! ## Weight congruence for a single expert-sum term -/

/-- If the two weight tensors agree on every index the term reads, the term
agrees.  Contrary to `moeGmmTerm_congr`, here the *token* data is fixed and the
*weights* move (and the two sides may sit at different `start`/`eLocal` as long
as `start + eLocal` coincides). -/
theorem moeGmmTerm_weight_congr
    (input rp rm w13 w2 w13' w2' : Tensor)
    (numExp start eLocal start' eLocal' l h_col hModel h_inner w13Mid : Nat)
    (swigluLimit : Scalar)
    (hexp : start + eLocal = start' + eLocal')
    (hw13 : ∀ j, j < w13Mid → ∀ k, k < hModel →
      valAt w13 ((eLocal * w13Mid + j) * hModel + k) =
        valAt w13' ((eLocal' * w13Mid + j) * hModel + k))
    (hw2 : ∀ dd, dd < h_inner →
      valAt w2 ((eLocal * hModel + h_col) * h_inner + dd) =
        valAt w2' ((eLocal' * hModel + h_col) * h_inner + dd))
    (hmid : 2 * h_inner ≤ w13Mid) :
    moeGmmTerm input rp rm w13 w2 numExp start eLocal l h_col hModel h_inner
        w13Mid swigluLimit
      = moeGmmTerm input rp rm w13' w2' numExp start' eLocal' l h_col hModel
        h_inner w13Mid swigluLimit := by
  unfold moeGmmTerm
  rw [hexp]
  by_cases h : valAt rm (l * numExp + (start' + eLocal')) = 0
  · simp only [h, if_pos]
  · simp only [h, if_false]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro dd hdd
    have hdd' : dd < h_inner := Finset.mem_range.mp hdd
    have hgate : (∑ k ∈ Finset.range hModel,
        valAt input (l * hModel + k) *
        valAt w13 ((eLocal * w13Mid + dd) * hModel + k))
        = ∑ k ∈ Finset.range hModel,
          valAt input (l * hModel + k) *
          valAt w13' ((eLocal' * w13Mid + dd) * hModel + k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hw13 dd (by omega) k (Finset.mem_range.mp hk)]
    have hup : (∑ k ∈ Finset.range hModel,
        valAt input (l * hModel + k) *
        valAt w13 ((eLocal * w13Mid + (h_inner + dd)) * hModel + k))
        = ∑ k ∈ Finset.range hModel,
          valAt input (l * hModel + k) *
          valAt w13' ((eLocal' * w13Mid + (h_inner + dd)) * hModel + k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hw13 (h_inner + dd) (by omega) k (Finset.mem_range.mp hk)]
    rw [hgate, hup, hw2 dd hdd']

/-- A term whose routing mask vanishes is zero. -/
theorem moeGmmTerm_of_mask_zero
    (input rp rm w13 w2 : Tensor)
    (numExp start eLocal l h_col hModel h_inner w13Mid : Nat)
    (swigluLimit : Scalar)
    (hmask : valAt rm (l * numExp + (start + eLocal)) = 0) :
    moeGmmTerm input rp rm w13 w2 numExp start eLocal l h_col hModel h_inner
      w13Mid swigluLimit = 0 := by
  unfold moeGmmTerm
  simp only [hmask, if_pos]

/-! ## The two collapse lemmas -/

section Collapse

variable (input rp rm w13_a w13_b w2_a w2_b : Tensor)
variable (L hM t_dim d_dim E topK : Nat) (swigluLimit : Scalar)

/-- Shape witnesses for the gathered `w13`. -/
private theorem head_w13 (hw13_a : w13_a.shape = [E, t_dim, hM]) :
    (([w13_a, w13_b] : List Tensor).head?.map (fun t => t.shape)).getD []
      = [E, t_dim, hM] := by
  simp only [List.head?_cons, Option.map_some, Option.getD_some, hw13_a]

private theorem head_w2 (hw2_a : w2_a.shape = [E, hM, d_dim]) :
    (([w2_a, w2_b] : List Tensor).head?.map (fun t => t.shape)).getD []
      = [E, hM, d_dim] := by
  simp only [List.head?_cons, Option.map_some, Option.getD_some, hw2_a]

/-- Shape of the gathered `w13`. -/
theorem gathered_w13_shape (hw13_a : w13_a.shape = [E, t_dim, hM]) :
    (allGatherPrimDimN 0 2 0 [w13_a, w13_b]).shape = [E * 2, t_dim, hM] := by
  rw [allGatherPrimDimN_shape 0 2 _ [E, t_dim, hM] (head_w13 w13_a w13_b hM t_dim E hw13_a)]
  simp only [List.set, List.getD_cons_zero]

set_option maxHeartbeats 1600000 in
/-- **Collapse, rank 0.**  A `[0, E)` expert-range operator on the *local*
weight shards equals the full `[0, 2*E)` operator on the *gathered* weights,
provided the routing map vanishes on the upper expert half. -/
theorem moe_gmm_lower_collapse
    (hL : 0 < L) (hhM : 0 < hM) (hE : 0 < E)
    (ht : 0 < t_dim) (hd : 0 < d_dim) (ht_even : t_dim = 2 * d_dim)
    (hinput : input.shape = [L, hM])
    (hrp : rp.shape = [L, E * 2])
    (hw13_a : w13_a.shape = [E, t_dim, hM]) (hw2_a : w2_a.shape = [E, hM, d_dim])
    (hdisj : ∀ l, l < L → ∀ e, E ≤ e → e < E * 2 →
      valAt rm (l * (E * 2) + e) = 0) :
    fw_all2all_moe_gmm input rp rm w13_a w2_a (E * 2) 0 E topK swigluLimit
      = fw_all2all_moe_gmm input rp rm
          (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
          (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
          (E * 2) 0 (E * 2) topK swigluLimit := by
  have hG13 : (allGatherPrimDimN 0 2 0 [w13_a, w13_b]).shape = [E * 2, t_dim, hM] :=
    gathered_w13_shape w13_a w13_b hM t_dim E hw13_a
  have hLshape := fw_all2all_moe_gmm_shape' input rp rm w13_a w2_a L hM (E * 2) 0 E
    topK swigluLimit hinput
  have hRshape := fw_all2all_moe_gmm_shape' input rp rm
    (allGatherPrimDimN 0 2 0 [w13_a, w13_b]) (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
    L hM (E * 2) 0 (E * 2) topK swigluLimit hinput
  refine Tensor.ext (by rw [hLshape, hRshape]) ?_
  intro idx hidx
  rw [hLshape, prodShape_2d'] at hidx
  set l := idx / hM with hldef
  set c := idx % hM with hcdef
  have hc : c < hM := Nat.mod_lt _ hhM
  have hl : l < L := (Nat.div_lt_iff_lt_mul hhM).mpr hidx
  have hidxEq : idx = l * hM + c := by
    rw [hldef, hcdef]; exact (Nat.div_add_mod' idx hM).symm
  rw [hidxEq]
  rw [fw_all2all_moe_gmm_valAt' input rp rm w13_a w2_a L hM (E * 2) E 0 E topK
    t_dim d_dim hhM ht_even hinput hrp hw13_a l hl c hc swigluLimit]
  rw [fw_all2all_moe_gmm_valAt' input rp rm _ _ L hM (E * 2) (E * 2) 0 (E * 2)
    topK t_dim d_dim hhM ht_even hinput hrp hG13 l hl c hc swigluLimit]
  rw [show E - 0 = E from by omega, show E * 2 - 0 = E + E from by omega]
  rw [Finset.sum_range_add]
  -- The shifted half vanishes by disjointness.
  have hzero : (∑ x ∈ Finset.range E,
      moeGmmTerm input rp rm (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
        (allGatherPrimDimN 0 2 0 [w2_a, w2_b]) (E * 2) 0 (E + x) l c hM
        d_dim t_dim swigluLimit) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hx' : x < E := Finset.mem_range.mp hx
    refine moeGmmTerm_of_mask_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    rw [show (0 : Nat) + (E + x) = E + x from Nat.zero_add _]
    exact hdisj l hl (E + x) (by omega) (by omega)
  rw [hzero, add_zero]
  -- The surviving half matches the local shard.
  refine (Finset.sum_congr rfl ?_).symm
  intro x hx
  have hx' : x < E := Finset.mem_range.mp hx
  refine (moeGmmTerm_weight_congr input rp rm w13_a w2_a _ _ (E * 2) 0 x 0 x l c
    hM d_dim t_dim swigluLimit rfl ?_ ?_ (by omega)).symm
  · intro j hj k hk
    have := allGather2_3d_valAt E t_dim hM hE ht hhM [w13_a, w13_b]
      (head_w13 w13_a w13_b hM t_dim E hw13_a) 0 (by omega) x hx' j hj k hk
    simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_zero] at this
    exact this.symm
  · intro dd hdd
    have := allGather2_3d_valAt E hM d_dim hE hhM hd [w2_a, w2_b]
      (head_w2 w2_a w2_b hM d_dim E hw2_a) 0 (by omega) x hx' c hc dd hdd
    simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_zero] at this
    exact this.symm

set_option maxHeartbeats 1600000 in
/-- **Collapse, rank 1.**  A `[E, 2*E)` expert-range operator on the *local*
weight shards equals the full `[0, 2*E)` operator on the *gathered* weights,
provided the routing map vanishes on the lower expert half. -/
theorem moe_gmm_upper_collapse
    (hL : 0 < L) (hhM : 0 < hM) (hE : 0 < E)
    (ht : 0 < t_dim) (hd : 0 < d_dim) (ht_even : t_dim = 2 * d_dim)
    (hinput : input.shape = [L, hM])
    (hrp : rp.shape = [L, E * 2])
    (hw13_b : w13_b.shape = [E, t_dim, hM]) (hw2_b : w2_b.shape = [E, hM, d_dim])
    (hw13_a : w13_a.shape = [E, t_dim, hM]) (hw2_a : w2_a.shape = [E, hM, d_dim])
    (hdisj : ∀ l, l < L → ∀ e, e < E → valAt rm (l * (E * 2) + e) = 0) :
    fw_all2all_moe_gmm input rp rm w13_b w2_b (E * 2) E (E * 2) topK swigluLimit
      = fw_all2all_moe_gmm input rp rm
          (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
          (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
          (E * 2) 0 (E * 2) topK swigluLimit := by
  have hG13 : (allGatherPrimDimN 0 2 0 [w13_a, w13_b]).shape = [E * 2, t_dim, hM] :=
    gathered_w13_shape w13_a w13_b hM t_dim E hw13_a
  have hLshape := fw_all2all_moe_gmm_shape' input rp rm w13_b w2_b L hM (E * 2) E
    (E * 2) topK swigluLimit hinput
  have hRshape := fw_all2all_moe_gmm_shape' input rp rm
    (allGatherPrimDimN 0 2 0 [w13_a, w13_b]) (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
    L hM (E * 2) 0 (E * 2) topK swigluLimit hinput
  refine Tensor.ext (by rw [hLshape, hRshape]) ?_
  intro idx hidx
  rw [hLshape, prodShape_2d'] at hidx
  set l := idx / hM with hldef
  set c := idx % hM with hcdef
  have hc : c < hM := Nat.mod_lt _ hhM
  have hl : l < L := (Nat.div_lt_iff_lt_mul hhM).mpr hidx
  have hidxEq : idx = l * hM + c := by
    rw [hldef, hcdef]; exact (Nat.div_add_mod' idx hM).symm
  rw [hidxEq]
  rw [fw_all2all_moe_gmm_valAt' input rp rm w13_b w2_b L hM (E * 2) E E (E * 2)
    topK t_dim d_dim hhM ht_even hinput hrp hw13_b l hl c hc swigluLimit]
  rw [fw_all2all_moe_gmm_valAt' input rp rm _ _ L hM (E * 2) (E * 2) 0 (E * 2)
    topK t_dim d_dim hhM ht_even hinput hrp hG13 l hl c hc swigluLimit]
  rw [show E * 2 - E = E from by omega, show E * 2 - 0 = E + E from by omega]
  rw [Finset.sum_range_add]
  -- The unshifted half vanishes by disjointness.
  have hzero : (∑ x ∈ Finset.range E,
      moeGmmTerm input rp rm (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
        (allGatherPrimDimN 0 2 0 [w2_a, w2_b]) (E * 2) 0 x l c hM
        d_dim t_dim swigluLimit) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hx' : x < E := Finset.mem_range.mp hx
    refine moeGmmTerm_of_mask_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    rw [show (0 : Nat) + x = x from Nat.zero_add _]
    exact hdisj l hl x hx'
  rw [hzero, zero_add]
  refine (Finset.sum_congr rfl ?_).symm
  intro x hx
  have hx' : x < E := Finset.mem_range.mp hx
  refine (moeGmmTerm_weight_congr input rp rm w13_b w2_b _ _ (E * 2) E x 0 (E + x)
    l c hM d_dim t_dim swigluLimit (by omega) ?_ ?_ (by omega)).symm
  · intro j hj k hk
    have := allGather2_3d_valAt E t_dim hM hE ht hhM [w13_a, w13_b]
      (head_w13 w13_a w13_b hM t_dim E hw13_a) 1 (by omega) x hx' j hj k hk
    simp only [Nat.one_mul, List.getD_cons_succ, List.getD_cons_zero] at this
    exact this.symm
  · intro dd hdd
    have := allGather2_3d_valAt E hM d_dim hE hhM hd [w2_a, w2_b]
      (head_w2 w2_a w2_b hM d_dim E hw2_a) 1 (by omega) x hx' c hc dd hdd
    simp only [Nat.one_mul, List.getD_cons_succ, List.getD_cons_zero] at this
    exact this.symm

end Collapse

/-! ## The main theorem -/

namespace Zigzag2Rel

set_option maxHeartbeats 1600000 in
/-- **Main theorem.**  The MoE expert layer preserves the CP2 zigzag layout in
the *real generated-graph* configuration: expert-range sharding
(`r0 = [0, E)`, `r1 = [E, 2*E)`, e.g. `E = 32`, `numExperts = 64`) with the
expert weights `w13`/`w2` themselves sharded over the two ranks, the SM side
reading their dim-0 all-gather.

The two `hrm*_disj` hypotheses are the honest side condition that makes
expert-range splitting sound at all: rank `r` may only ever be asked to
evaluate experts it actually owns, so its (post-shuffle) routing map must be
zero on the other rank's expert half. -/
theorem all2all_moe_gmm_expert_split_cp2
    {fx frp frm zx0 zx1 zrp0 zrp1 zrm0 zrm1 cu : Tensor}
    (w13_a w13_b w2_a w2_b : Tensor)
    (lDim hModel E topK t_dim d_dim : Nat) (swigluLimit : Scalar)
    (hrelX : Zigzag2Rel fx zx0 zx1 cu [lDim * 2, hModel] [lDim, hModel])
    (hrelRP : Zigzag2Rel frp zrp0 zrp1 cu [lDim * 2, E * 2] [lDim, E * 2])
    (hrelRM : Zigzag2Rel frm zrm0 zrm1 cu [lDim * 2, E * 2] [lDim, E * 2])
    (hl : 0 < lDim) (heven : lDim % 2 = 0)
    (hhModel : 0 < hModel) (hE : 0 < E)
    (ht : 0 < t_dim) (hd : 0 < d_dim) (ht_even : t_dim = 2 * d_dim)
    (hw13_a : w13_a.shape = [E, t_dim, hModel])
    (hw13_b : w13_b.shape = [E, t_dim, hModel])
    (hw2_a : w2_a.shape = [E, hModel, d_dim])
    (hw2_b : w2_b.shape = [E, hModel, d_dim])
    (hrm0_disj : ∀ l, l < lDim → ∀ e, E ≤ e → e < E * 2 →
      valAt zrm0 (l * (E * 2) + e) = 0)
    (hrm1_disj : ∀ l, l < lDim → ∀ e, e < E → valAt zrm1 (l * (E * 2) + e) = 0)
    (hdec : decodeCuSeqlens cu = [0, 2 * lDim]) :
    Zigzag2Rel
      (fw_all2all_moe_gmm fx frp frm
        (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
        (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
        (E * 2) 0 (E * 2) topK swigluLimit)
      (fw_all2all_moe_gmm zx0 zrp0 zrm0 w13_a w2_a (E * 2) 0 E topK swigluLimit)
      (fw_all2all_moe_gmm zx1 zrp1 zrm1 w13_b w2_b (E * 2) E (E * 2) topK
        swigluLimit)
      cu [lDim * 2, hModel] [lDim, hModel] := by
  have hx0 : zx0.shape = [lDim, hModel] := hrelX.rank0_shape
  have hx1 : zx1.shape = [lDim, hModel] := hrelX.rank1_shape
  have hrp0 : zrp0.shape = [lDim, E * 2] := hrelRP.rank0_shape
  have hrp1 : zrp1.shape = [lDim, E * 2] := hrelRP.rank1_shape
  have hG13 : (allGatherPrimDimN 0 2 0 [w13_a, w13_b]).shape
      = [E * 2, t_dim, hModel] :=
    gathered_w13_shape w13_a w13_b hModel t_dim E hw13_a
  rw [moe_gmm_lower_collapse zx0 zrp0 zrm0 w13_a w13_b w2_a w2_b lDim hModel
    t_dim d_dim E topK swigluLimit hl hhModel hE ht hd ht_even hx0 hrp0
    hw13_a hw2_a hrm0_disj]
  rw [moe_gmm_upper_collapse zx1 zrp1 zrm1 w13_a w13_b w2_a w2_b lDim hModel
    t_dim d_dim E topK swigluLimit hl hhModel hE ht hd ht_even hx1 hrp1
    hw13_b hw2_b hw13_a hw2_a hrm1_disj]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [w13_a, w13_b])
    (allGatherPrimDimN 0 2 0 [w2_a, w2_b])
    lDim hModel (E * 2) topK (E * 2) t_dim d_dim swigluLimit
    hrelX hrelRP hrelRM hl heven hhModel (by omega) ht_even hG13 hdec

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
