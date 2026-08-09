/- Layout-neutral tensor semantics for the faithful two-rank full-expert MoE commute. -/
import denote.DenoteMoE
import denote.Gather2Rel

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote

noncomputable section

/-- The MoE `fw_all2all_moe_gmm` sum body at fixed (l, h_col, eLocal), abstracted for reuse.
    Note: routing indices use `e = start + eLocal` while weight indices use `eLocal` directly. -/
noncomputable def moe_gmm_term
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

/-- `moe_gmm_term` is congruent under equal valAt of all its inputs at relevant indices.
    Both sides use the same `eLocal` — this is a "same body, different tensors" lemma. -/
theorem moe_gmm_term_congr
    (input₁ rp₁ rm₁ w13₁ w2₁ input₂ rp₂ rm₂ w13₂ w2₂ : Tensor)
    (numExp start eLocal l₁ l₂ h_col hModel h_inner w13Mid : Nat)
    (swigluLimit : Scalar)
    (hmask : valAt rm₁ (l₁ * numExp + (start + eLocal)) = valAt rm₂ (l₂ * numExp + (start + eLocal)))
    (hprob : valAt rp₁ (l₁ * numExp + (start + eLocal)) = valAt rp₂ (l₂ * numExp + (start + eLocal)))
    (hinput : ∀ k, k < hModel → valAt input₁ (l₁ * hModel + k) = valAt input₂ (l₂ * hModel + k))
    (hw13 : ∀ d k, d < h_inner → k < hModel →
      valAt w13₁ ((eLocal * w13Mid + d) * hModel + k) = valAt w13₂ ((eLocal * w13Mid + d) * hModel + k))
    (hw13' : ∀ d k, d < h_inner → k < hModel →
      valAt w13₁ ((eLocal * w13Mid + (h_inner + d)) * hModel + k) = valAt w13₂ ((eLocal * w13Mid + (h_inner + d)) * hModel + k))
    (hw2 : ∀ d, d < h_inner →
      valAt w2₁ ((eLocal * hModel + h_col) * h_inner + d) = valAt w2₂ ((eLocal * hModel + h_col) * h_inner + d)) :
    moe_gmm_term input₁ rp₁ rm₁ w13₁ w2₁ numExp start eLocal l₁ h_col hModel h_inner w13Mid swigluLimit
      = moe_gmm_term input₂ rp₂ rm₂ w13₂ w2₂ numExp start eLocal l₂ h_col hModel h_inner w13Mid swigluLimit := by
  unfold moe_gmm_term
  simp only [hmask]
  by_cases h : valAt rm₂ (l₂ * numExp + (start + eLocal)) = 0
  · simp [h]
  · simp only [h, if_false]
    rw [hprob]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    have hd_lt : d < h_inner := by simp [Finset.mem_range] at hd; exact hd
    have hgate_eq : (∑ k ∈ Finset.range hModel,
        valAt input₁ (l₁ * hModel + k) *
        valAt w13₁ ((eLocal * w13Mid + d) * hModel + k))
        = ∑ k ∈ Finset.range hModel,
          valAt input₂ (l₂ * hModel + k) *
          valAt w13₂ ((eLocal * w13Mid + d) * hModel + k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk_lt : k < hModel := by simp [Finset.mem_range] at hk; exact hk
      rw [hinput k hk_lt, hw13 d k hd_lt hk_lt]
    have hup_eq : (∑ k ∈ Finset.range hModel,
        valAt input₁ (l₁ * hModel + k) *
        valAt w13₁ ((eLocal * w13Mid + (h_inner + d)) * hModel + k))
        = ∑ k ∈ Finset.range hModel,
          valAt input₂ (l₂ * hModel + k) *
          valAt w13₂ ((eLocal * w13Mid + (h_inner + d)) * hModel + k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk_lt : k < hModel := by simp [Finset.mem_range] at hk; exact hk
      rw [hinput k hk_lt, hw13' d k hd_lt hk_lt]
    rw [hgate_eq, hup_eq, hw2 d hd_lt]

/-- `fw_all2all_moe_gmm` value at flat idx `l * hModel + h_col` (with `l < lDim, h_col < hModel`)
    equals the sum of `moe_gmm_term` over the local expert range. -/
theorem fw_all2all_moe_gmm_valAt
    (input rp rm w13 w2 : Tensor)
    (L hModel numExp E_total start endE topK t_dim d_dim : Nat)
    (hL : 0 < L) (hhModel : 0 < hModel) (hnE : 0 < numExp) (hE_total : 0 < E_total)
    (hstart_le_end : start ≤ endE)
    (ht_even : t_dim = 2 * d_dim)
    (hinput_shape : input.shape = [L, hModel])
    (hrp_shape : rp.shape = [L, numExp])
    (hw13_shape : w13.shape = [E_total, t_dim, hModel])
    (l : Nat) (hl : l < L) (h_col : Nat) (hh_col : h_col < hModel)
    (swigluLimit : Scalar) :
    valAt (fw_all2all_moe_gmm input rp rm w13 w2 numExp start endE topK swigluLimit) (l * hModel + h_col)
      = ∑ eLocal ∈ Finset.range (endE - start),
          moe_gmm_term input rp rm w13 w2 numExp start eLocal l h_col hModel d_dim t_dim swigluLimit := by
  unfold fw_all2all_moe_gmm
  simp only [Tensor.mkShape, valAt]
  -- Bound check for dif_pos
  have hbound : l * hModel + h_col < prodShape [(input.shape.head?).getD 0, (input.shape.reverse.head?).getD 0] := by
    rw [hinput_shape]
    simp [prodShape, List.reverse_cons]
    calc l * hModel + h_col < l * hModel + hModel := by omega
      _ = (l + 1) * hModel := by ring
      _ ≤ L * hModel := Nat.mul_le_mul_right _ (by omega)
  rw [dif_pos hbound]
  -- Now the RHS of the equality is the sum expressed in terms of moe_gmm_term
  -- After simp/unfold, LHS also becomes the same sum structure
  -- The key is that hModel, w13Mid, h_inner, numExp all resolve to what moe_gmm_term expects
  have hModel_eq : (input.shape.reverse.head?).getD 0 = hModel := by
    rw [hinput_shape]; simp
  have hw13Mid_eq : (w13.shape.drop 1).head?.getD 0 = t_dim := by
    rw [hw13_shape]; simp
  have hnumExp_eq : (rp.shape.drop 1).head?.getD 0 = numExp := by
    rw [hrp_shape]; simp
  have hlDim_eq : (input.shape.head?).getD 0 = L := by
    rw [hinput_shape]; simp
  have hh_inner_eq : t_dim / 2 = d_dim := by rw [ht_even]; omega
  -- The valAt (h_col comes from l*hModel+h_col) — compute h = idx % hModel, l' = idx / hModel
  have hh_eq : (l * hModel + h_col) % hModel = h_col := by
    have h1 : (l * hModel + h_col) % hModel = h_col % hModel := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h1, Nat.mod_eq_of_lt hh_col]
  have hl'_eq : (l * hModel + h_col) / hModel = l := by
    have h1 : (l * hModel + h_col) / hModel = h_col / hModel + l := by
      rw [Nat.add_comm, Nat.add_mul_div_right h_col l hhModel]
    rw [h1, Nat.div_eq_of_lt hh_col]; ring
  -- Now expand both sides via the moe_gmm_term unfolding
  unfold moe_gmm_term
  simp only [hModel_eq, hw13Mid_eq, hnumExp_eq, hh_inner_eq, hh_eq, hl'_eq]
  -- Both sides are now sums; the body has raw `if h : ... then val else 0` on LHS
  -- and `valAt` on RHS. Unfold valAt so both match.
  simp only [valAt]

/-! ### Upstream-faithful sharding-commute for `fw_all2all_moe_gmm_full`.

The old `fw_all2all_moe_gmm_split_commute_2_of` theorem (still below for legacy
reference) proves the sharding commute for `fw_all2all_moe_gmm` (the per-rank
partial variant), but required routing-map disjointness axioms
(`Pattern_1_rma/rmbDisjointAxiom`) that were themselves vacuous — universally
quantified over routing_map without any binding to the actual dispatched form.

The upstream-faithful `fw_all2all_moe_gmm_full` doesn't have this problem:
both LHS and RHS sum over the FULL expert range `[0, numExp)` using the same
gathered `w13_full`/`w2_full` weights. The sharding commute reduces to
"input/rp/rm split along L axis + gather = identity at each L slot".

DELETED: `Pattern_1_rmaDisjointAxiom` and `Pattern_1_rmbDisjointAxiom` — no
longer needed because the disjointness constraint is now encoded
by-construction in the allGather layout of `w13s`/`w2s`. -/

/-- Bridge lemma: `fw_all2all_moe_gmm` on gathered weights (same numRanks for
    both w13s and w2s) = `fw_all2all_moe_gmm_full` on the shard lists. Follows
    from `_full`'s definition (gather-then-call-old-kernel). Requires
    `w13s.length = w2s.length` because the two `numRanks` in the RHS come from
    the same `let` in `_full`. -/
theorem fw_all2all_moe_gmm_eq_full_on_shards
    (input rp rm : Tensor) (w13s w2s : List Tensor)
    (numExp topK : Nat) (swigluLimit : Scalar)
    (hlen : w13s.length = w2s.length) :
    fw_all2all_moe_gmm input rp rm
        (allGatherPrimDimN 0 w13s.length 0 w13s)
        (allGatherPrimDimN 0 w2s.length 0 w2s)
        numExp 0 numExp topK swigluLimit
      = fw_all2all_moe_gmm_full input rp rm w13s w2s numExp topK swigluLimit := by
  unfold fw_all2all_moe_gmm_full
  rw [hlen]

/-- Upstream-faithful sharding commute for `fw_all2all_moe_gmm_full` when
    inputs/routing tensors are split along L axis across 2 ranks, weights
    already in per-rank shard form. Statement: gather-of-inputs, applied to
    full kernel with sharded weights, equals gather-of-per-rank-outputs
    (each per-rank output uses the same weight shards).

    Provable pointwise: kernel body at output flat idx `l * hM + h` only
    reads row `l` of input/rp/rm. Both sides use identical
    `allGatherPrimDimN 0 2 0 [w13_a, w13_b]` (and w2). LHS's `l ∈ [0, 2L)`
    splits by allGather into `l < L → in_a[l]` vs `l ≥ L → in_b[l-L]`; RHS
    mirrors via its own gather. No disjointness needed.

    The pointwise proof is semantic and layout-neutral: it assumes no
    Pattern-specific facts and needs no routing disjointness hypothesis. -/
theorem fw_all2all_moe_gmm_full_split_commute_2
    (input_a input_b rp_a rp_b rm_a rm_b w13_a w13_b w2_a w2_b : Tensor)
    (L hM E_shard topK t_dim d_dim : Nat) (swigluLimit : Scalar)
    (hL : 0 < L) (hhM : 0 < hM) (hE : 0 < E_shard) (ht : 0 < t_dim) (hd : 0 < d_dim)
    (ht_even : t_dim = 2 * d_dim)
    (hinput_a : input_a.shape = [L, hM]) (hinput_b : input_b.shape = [L, hM])
    (hrp_a : rp_a.shape = [L, E_shard * 2]) (hrp_b : rp_b.shape = [L, E_shard * 2])
    (hrm_a : rm_a.shape = [L, E_shard * 2]) (hrm_b : rm_b.shape = [L, E_shard * 2])
    (hw13_a : w13_a.shape = [E_shard, t_dim, hM]) (hw13_b : w13_b.shape = [E_shard, t_dim, hM])
    (hw2_a : w2_a.shape = [E_shard, hM, d_dim]) (hw2_b : w2_b.shape = [E_shard, hM, d_dim]) :
    fw_all2all_moe_gmm_full
        (allGatherPrimDimN 0 2 0 [input_a, input_b])
        (allGatherPrimDimN 0 2 0 [rp_a, rp_b])
        (allGatherPrimDimN 0 2 0 [rm_a, rm_b])
        [w13_a, w13_b] [w2_a, w2_b]
        (E_shard * 2) topK swigluLimit
      = allGatherPrimDimN 0 2 0
          [fw_all2all_moe_gmm_full input_a rp_a rm_a [w13_a, w13_b] [w2_a, w2_b]
              (E_shard * 2) topK swigluLimit,
           fw_all2all_moe_gmm_full input_b rp_b rm_b [w13_a, w13_b] [w2_a, w2_b]
              (E_shard * 2) topK swigluLimit] := by
  -- Unfold both sides to `fw_all2all_moe_gmm` on gathered w13/w2 (same weights).
  unfold fw_all2all_moe_gmm_full
  -- Reduce list length to numeric 2.
  simp only [List.length_cons, List.length_nil, show (0 + 1 + 1 : Nat) = 2 from rfl]
  -- Setup local abbreviations
  set numExp := E_shard * 2 with hnumExp_def
  have hnE : 0 < numExp := by rw [hnumExp_def]; positivity
  set gW13 := allGatherPrimDimN 0 2 0 [w13_a, w13_b] with hgW13_def
  set gW2 := allGatherPrimDimN 0 2 0 [w2_a, w2_b] with hgW2_def
  -- Shape witnesses for allGathers
  have hhead_input : (([input_a, input_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, hM] := by simp [hinput_a]
  have hshapes_input : ∀ r' (_ : r' < 2), (([input_a, input_b].getD r' (zeroTensor [L, hM]))).shape = [L, hM] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hinput_a, hinput_b]
  have hhead_rp : (([rp_a, rp_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, numExp] := by
    simp [hrp_a, hnumExp_def]
  have hshapes_rp : ∀ r' (_ : r' < 2), (([rp_a, rp_b].getD r' (zeroTensor [L, numExp]))).shape = [L, numExp] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hrp_a, hrp_b, hnumExp_def]
  have hhead_rm : (([rm_a, rm_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, numExp] := by
    simp [hrm_a, hnumExp_def]
  have hshapes_rm : ∀ r' (_ : r' < 2), (([rm_a, rm_b].getD r' (zeroTensor [L, numExp]))).shape = [L, numExp] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hrm_a, hrm_b, hnumExp_def]
  -- Gathered input shape [L*2, hM]
  have hG_input : (allGatherPrimDimN 0 2 0 [input_a, input_b]).shape = [L * 2, hM] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, hM] hhead_input]; simp [List.set, List.getD]
  have hG_rp : (allGatherPrimDimN 0 2 0 [rp_a, rp_b]).shape = [L * 2, numExp] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, numExp] hhead_rp]; simp [List.set, List.getD]
  have hG_rm : (allGatherPrimDimN 0 2 0 [rm_a, rm_b]).shape = [L * 2, numExp] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, numExp] hhead_rm]; simp [List.set, List.getD]
  -- Per-rank local moe_gmm output shape [L, hM] (uses gathered gW13/gW2)
  have hloc_a_shape : (fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2
                        numExp 0 numExp topK swigluLimit).shape = [L, hM] := by
    unfold fw_all2all_moe_gmm
    show (Tensor.mkShape [_, _] _).shape = _
    simp only [Tensor.mkShape]; rw [hinput_a]; rfl
  have hloc_b_shape : (fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2
                        numExp 0 numExp topK swigluLimit).shape = [L, hM] := by
    unfold fw_all2all_moe_gmm
    show (Tensor.mkShape [_, _] _).shape = _
    simp only [Tensor.mkShape]; rw [hinput_b]; rfl
  have hhead_loc : (([fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
                      fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit] : List Tensor).head?.map (fun t => t.shape)).getD [] = [L, hM] := by
    simp [hloc_a_shape]
  have hshapes_loc : ∀ r' (_ : r' < 2),
      (([fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
         fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit].getD r' (zeroTensor [L, hM]))).shape = [L, hM] := by
    intro r' hr'; have : r' = 0 ∨ r' = 1 := by interval_cases r' <;> [left; right] <;> rfl
    rcases this with h | h <;> rw [h] <;> simp [List.getD, hloc_a_shape, hloc_b_shape]
  -- LHS / RHS overall shape [L*2, hM]
  have hLHS_shape : (fw_all2all_moe_gmm (allGatherPrimDimN 0 2 0 [input_a, input_b])
        (allGatherPrimDimN 0 2 0 [rp_a, rp_b])
        (allGatherPrimDimN 0 2 0 [rm_a, rm_b])
        gW13 gW2 numExp 0 numExp topK swigluLimit).shape = [L * 2, hM] := by
    unfold fw_all2all_moe_gmm
    show (Tensor.mkShape [_, _] _).shape = _
    simp only [Tensor.mkShape]; rw [hG_input]; rfl
  have hRHS_shape : (allGatherPrimDimN 0 2 0
        [fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
         fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit]).shape = [L * 2, hM] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, hM] hhead_loc]; simp [List.set, List.getD]
  -- Prove tensor equality: shape equal + pointwise value equal
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro outIdx houtIdx
    rw [hLHS_shape] at houtIdx
    have houtIdx_bound : outIdx < L * 2 * hM := by simpa [prodShape] using houtIdx
    -- Decompose outIdx into (row, col) then (r, i)
    set row := outIdx / hM with hrow_def
    set col := outIdx % hM with hcol_def
    have hcol_lt : col < hM := by rw [hcol_def]; exact Nat.mod_lt _ hhM
    have hrow_lt : row < L * 2 := by
      rw [hrow_def]; rw [Nat.div_lt_iff_lt_mul hhM]; linarith
    have houtIdx_eq : outIdx = row * hM + col := by
      have h1 : hM * (outIdx / hM) + outIdx % hM = outIdx := Nat.div_add_mod outIdx hM
      rw [hrow_def, hcol_def]
      linarith [Nat.mul_comm hM (outIdx / hM)]
    set r := row / L with hr_def
    set i := row % L with hi_def
    have hi_lt : i < L := by rw [hi_def]; exact Nat.mod_lt _ hL
    have hr_lt : r < 2 := by
      rw [hr_def]; rw [Nat.div_lt_iff_lt_mul hL]; linarith
    have hrow_eq : row = r * L + i := by
      have h1 : L * (row / L) + row % L = row := Nat.div_add_mod row L
      rw [hr_def, hi_def]
      linarith [Nat.mul_comm L (row / L)]
    -- Set arithmetic for both sides
    rw [houtIdx_eq, hrow_eq]
    have hrow_lt' : r * L + i < L * 2 := by
      calc r * L + i < r * L + L := by omega
        _ = (r + 1) * L := by ring
        _ ≤ 2 * L := Nat.mul_le_mul_right _ (by omega)
        _ = L * 2 := by ring
    -- LHS valAt using fw_all2all_moe_gmm_valAt (need gW13 shape to obtain t_dim/d_dim decoding)
    have hG_w13 : gW13.shape = [E_shard * 2, t_dim, hM] := by
      rw [hgW13_def]
      have hhead_w13 : (([w13_a, w13_b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [E_shard, t_dim, hM] := by simp [hw13_a]
      rw [allGatherPrimDimN_shape 0 2 _ [E_shard, t_dim, hM] hhead_w13]; simp [List.set, List.getD]
    -- Apply fw_all2all_moe_gmm_valAt to LHS with lDim = L*2 (gathered).
    rw [fw_all2all_moe_gmm_valAt _ _ _ _ _ (L * 2) hM numExp (E_shard * 2) 0 numExp topK t_dim d_dim
        (by omega) hhM hnE (by omega) (by omega) ht_even hG_input hG_rp hG_w13
        (r * L + i) hrow_lt' col hcol_lt swigluLimit]
    -- Apply allGatherPrimDimN0_valAt to RHS's outer allGather.
    rw [allGatherPrimDimN0_valAt 2 L hM
        [fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
         fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit]
        (by omega) hL hhM hhead_loc hshapes_loc r hr_lt i hi_lt col hcol_lt]
    -- Case on r=0 vs r=1
    have hr_cases : r = 0 ∨ r = 1 := by interval_cases r <;> [left; right] <;> rfl
    rcases hr_cases with hr0 | hr1
    · -- Case r = 0: RHS = shard 0's moe_gmm on in_a rp_a rm_a with gW13/gW2, sum range [0, numExp)
      rw [hr0]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show ([fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
                 fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit].getD 0 (zeroTensor [L, hM]))
                = fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit from rfl]
      rw [fw_all2all_moe_gmm_valAt input_a rp_a rm_a gW13 gW2
          L hM numExp (E_shard * 2) 0 numExp topK t_dim d_dim
          hL hhM hnE (by omega) (by omega) ht_even hinput_a hrp_a hG_w13 i hi_lt col hcol_lt swigluLimit]
      -- Both sides: ∑ eLocal ∈ range numExp, moe_gmm_term (X, ..., 0, eLocal, l, col, ...) where l is:
      -- LHS: l = 0*L + i (needs simp)
      -- RHS: l = i
      -- All other args (numExp/start=0/eLocal/hM/d_dim/t_dim/sl) match. Weights (gW13, gW2) same.
      -- Only differ in input/rp/rm: LHS = gather0'd, RHS = a's raw.
      have hsub_zero : E_shard * 2 - 0 = E_shard * 2 := by omega
      rw [hsub_zero]
      apply Finset.sum_congr rfl
      intro x hx
      have hx_lt : x < E_shard * 2 := by simp [Finset.mem_range] at hx; exact hx
      have h_bound_e : 0 + x < numExp := by rw [hnumExp_def]; omega
      apply moe_gmm_term_congr
      · -- hmask: valAt (gather0 rm) (i * numExp + (0+x)) = valAt rm_a (i * numExp + (0+x))
        have := allGatherPrimDimN0_valAt 2 L numExp
            [rm_a, rm_b]
            (by omega) hL hnE hhead_rm hshapes_rm 0 (by omega) i hi_lt (0 + x) h_bound_e
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl] at this
        -- `this` is now (i * numExp + x) form; need to expose `(0 + x)` to match moe_gmm_term_congr
        rw [show x = 0 + x from (Nat.zero_add x).symm] at this
        exact this
      · -- hprob: valAt (gather0 rp) (i * numExp + (0+x)) = valAt rp_a (i * numExp + (0+x))
        have := allGatherPrimDimN0_valAt 2 L numExp
            [rp_a, rp_b]
            (by omega) hL hnE hhead_rp hshapes_rp 0 (by omega) i hi_lt (0 + x) h_bound_e
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl] at this
        rw [show x = 0 + x from (Nat.zero_add x).symm] at this
        exact this
      · -- hinput: valAt (gather0 input) (i * hM + k) = valAt input_a (i * hM + k)
        intro k hk
        have := allGatherPrimDimN0_valAt 2 L hM
            [input_a, input_b]
            (by omega) hL hhM hhead_input hshapes_input 0 (by omega) i hi_lt k hk
        simp only [Nat.zero_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 0 d = t₁ from fun _ _ _ => rfl] at this
        exact this
      · -- hw13: gW13 = gW13 (both sides use same gathered w13) — trivially rfl
        intro _ _ _ _; rfl
      · -- hw13': same as hw13 (trivial rfl)
        intro _ _ _ _; rfl
      · -- hw2: same as hw13 (both use gW2)
        intro _ _; rfl
    · -- Case r = 1: RHS = shard 1's moe_gmm on in_b rp_b rm_b with gW13/gW2, sum range [0, numExp)
      rw [hr1]
      simp only [Nat.one_mul]
      rw [show ([fw_all2all_moe_gmm input_a rp_a rm_a gW13 gW2 numExp 0 numExp topK swigluLimit,
                 fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit].getD 1 (zeroTensor [L, hM]))
                = fw_all2all_moe_gmm input_b rp_b rm_b gW13 gW2 numExp 0 numExp topK swigluLimit from rfl]
      rw [fw_all2all_moe_gmm_valAt input_b rp_b rm_b gW13 gW2
          L hM numExp (E_shard * 2) 0 numExp topK t_dim d_dim
          hL hhM hnE (by omega) (by omega) ht_even hinput_b hrp_b hG_w13 i hi_lt col hcol_lt swigluLimit]
      have hsub_zero : E_shard * 2 - 0 = E_shard * 2 := by omega
      rw [hsub_zero]
      apply Finset.sum_congr rfl
      intro x hx
      have hx_lt : x < E_shard * 2 := by simp [Finset.mem_range] at hx; exact hx
      have h_bound_e : 0 + x < numExp := by rw [hnumExp_def]; omega
      apply moe_gmm_term_congr
      · -- hmask: valAt (gather0 rm) ((1*L+i) * numExp + (0+x)) = valAt rm_b (i * numExp + (0+x))
        have := allGatherPrimDimN0_valAt 2 L numExp
            [rm_a, rm_b]
            (by omega) hL hnE hhead_rm hshapes_rm 1 (by omega) i hi_lt (0 + x) h_bound_e
        simp only [Nat.one_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        rw [show x = 0 + x from (Nat.zero_add x).symm] at this
        exact this
      · -- hprob
        have := allGatherPrimDimN0_valAt 2 L numExp
            [rp_a, rp_b]
            (by omega) hL hnE hhead_rp hshapes_rp 1 (by omega) i hi_lt (0 + x) h_bound_e
        simp only [Nat.one_mul, Nat.zero_add,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        rw [show x = 0 + x from (Nat.zero_add x).symm] at this
        exact this
      · -- hinput
        intro k hk
        have := allGatherPrimDimN0_valAt 2 L hM
            [input_a, input_b]
            (by omega) hL hhM hhead_input hshapes_input 1 (by omega) i hi_lt k hk
        simp only [Nat.one_mul,
                   show ∀ (t₁ t₂ : Tensor) (d : Tensor), ([t₁, t₂] : List Tensor).getD 1 d = t₂ from fun _ _ _ => rfl] at this
        exact this
      · intro _ _ _ _; rfl
      · intro _ _ _ _; rfl
      · intro _ _; rfl


/-- Parameterized full-expert 2TP MoE boundary gear. Graph-specific work is
    isolated in the three node-value equations. -/
theorem gather2Rel_fullExpertMoE_boundary
    (input input0 input1 rp rp0 rp1 rm rm0 rm1
      w130 w131 w20 w21 out out0 out1 : Tensor)
    (L hM E topK tDim dDim : Nat) (swigluLimit : Scalar)
    (hL : 0 < L) (hhM : 0 < hM) (hE : 0 < E)
    (ht : 0 < tDim) (hd : 0 < dDim) (hteven : tDim = 2 * dDim)
    (hinput : Gather2Rel input input0 input1 [L * 2, hM] [L, hM])
    (hrp : Gather2Rel rp rp0 rp1 [L * 2, E * 2] [L, E * 2])
    (hrm : Gather2Rel rm rm0 rm1 [L * 2, E * 2] [L, E * 2])
    (hw130 : w130.shape = [E, tDim, hM]) (hw131 : w131.shape = [E, tDim, hM])
    (hw20 : w20.shape = [E, hM, dDim]) (hw21 : w21.shape = [E, hM, dDim])
    (hfullNode : out = fw_all2all_moe_gmm_full input rp rm
      [w130, w131] [w20, w21] (E * 2) topK swigluLimit)
    (hnode0 : out0 = fw_all2all_moe_gmm_full input0 rp0 rm0
      [w130, w131] [w20, w21] (E * 2) topK swigluLimit)
    (hnode1 : out1 = fw_all2all_moe_gmm_full input1 rp1 rm1
      [w130, w131] [w20, w21] (E * 2) topK swigluLimit)
    (houtShape : out.shape = [L * 2, hM])
    (hout0Shape : out0.shape = [L, hM]) (hout1Shape : out1.shape = [L, hM]) :
    Gather2Rel out out0 out1 [L * 2, hM] [L, hM] := by
  refine ⟨?_, houtShape, hout0Shape, hout1Shape, ?_⟩
  · rw [hfullNode, hnode0, hnode1, hinput.value, hrp.value, hrm.value]
    exact fw_all2all_moe_gmm_full_split_commute_2
      input0 input1 rp0 rp1 rm0 rm1 w130 w131 w20 w21
      L hM E topK tDim dDim swigluLimit hL hhM hE ht hd hteven
      hinput.shard0_shape hinput.shard1_shape
      hrp.shard0_shape hrp.shard1_shape hrm.shard0_shape hrm.shard1_shape
      hw130 hw131 hw20 hw21
  · intro heq
    have hlen := congrArg List.length heq
    norm_num at hlen

#print axioms fw_all2all_moe_gmm_full_split_commute_2
#print axioms gather2Rel_fullExpertMoE_boundary


end
end TrainVerify.Denote.GeneratedPatterns
