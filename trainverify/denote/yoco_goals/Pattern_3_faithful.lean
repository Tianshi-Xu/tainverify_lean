/-
  Pattern_3_faithful.lean — 2026-07-06 upstream-reshape-fidelity variant of Pattern_3.

  This is the FROM-SCRATCH proof of `prove_pattern_3` built on top of Goal_3_faithful,
  which carries FW_reshape target shape params (unlike legacy Goal_3.lean whose
  reshape params were empty, making them identity-modelled in Denote).

  The old Pattern_3.lean (12k+ lines) is preserved untouched: it uses the OLD
  identity FW_reshape semantics and its already-proven L0/L1 lemmas remain
  formally valid but the `prove_goal_3` sorry there is UNPROVABLE because under
  identity reshape, `goal_3_stmt_cut_ringAttn` is mathematically false at
  layers ≥ 2 (see ANALYSIS_V2.md for the full root-cause chain).

  Under the new faithful reshape:
  - reshape [4096, 16, 64] → [4096, 1024] genuinely flattens head+dim,
    letting the downstream fw_linear go through the 2D branch,
    and the subsequent fw_view [4096, 1024] becomes a no-op.
  - SM: reshape-then-linear-then-view = reshape-flatten-then-linear-2D-then-noop.
  - PM: same on shards + allGather, and gather-then-reshape ≡ reshape-then-gather
    on shard-dim-0 (because reshape flattens preserving shard-0 semantics).
  - Hence sm_pm_router_L{k}_commute is TRUE for k = 0..23.

  Namespace: `TrainVerify.Denote.Pattern3Faithful`, disambiguated from
  `TrainVerify.Denote.Pattern3` in the legacy Pattern_3.lean.
-/
import denote.yoco_goals.Goal_3_faithful
import denote.yoco_goals.Pattern_1  -- reuse fw_topk_routing_snd_fst_allGather0_commute_2_of

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoalsFaithful

namespace TrainVerify.Denote.Pattern3Faithful

/-! ## Layer-step commute skeleton

    For each layer k ∈ {0, 1, ..., 23}, we need:
    - `sm_pm_router_Lk_commute` : SM router output at layer k equals allGather0 of PM shards
    - `sm_pm_carry_Lk_commute`  : SM residual carry equals allGather0 of PM carry
    - `sm_pm_attn_Lk_commute`   : SM attention output equals allGather0 of PM attn shards
    - `sm_pm_qproj_Lk_commute` / `_kproj_Lk_commute` / `_vproj_Lk_commute`
       (only for layers where q/k/v are shard-computed rather than chunk-of-SM)

    Then `sm_pm_final_stack_commute` assembles the 24-layer outputs into 4675,
    and `prove_goal_3` closes the goal_3_stmt_cut_ringAttn Prop.

    The current file has ONLY the top-level `prove_pattern_3` skeleton; individual
    layer commute lemmas are to be filled in by the copilot worker per PROMPT.md.
-/

/-! ## Ring-fold utility lemmas (graph-independent; copied from legacy Pattern_3). -/

theorem foldl_take_split_at_not_written_ringAttn
    (g : GraphDecl) (nodes : List NodeDecl)
    (s : Store) (tid : Tid) (j k : Nat) (hjk : j ≤ k)
    (hnil : ∀ n ∈ (nodes.take k).drop j, n.outs ≠ [])
    (h : ∀ n ∈ (nodes.take k).drop j, tid ∉ n.outs) :
    (nodes.take k).foldl (applyNodeRingAttn g) s tid =
      (nodes.take j).foldl (applyNodeRingAttn g) s tid := by
  have h_split : nodes.take k = nodes.take j ++ (nodes.take k).drop j := by
    rw [show nodes.take j = (nodes.take k).take j by rw [List.take_take, min_eq_left hjk]]
    rw [List.take_append_drop]
  rw [h_split, List.foldl_append]
  exact foldl_applyNodeRingAttn_at_not_written g _ _ tid hnil h

/-- Entry bridge: the value at `tid` in the full-graph ring-fold equals its
    value after the prefix `nodes.take k`, provided no node in the suffix
    `nodes.drop k` writes `tid`. Used once per target tid to jump from the full
    903/1866-node graph down to the small dependency-cone prefix, after which
    `foldl_take_split_at_not_written_ringAttn` handles the body. -/
theorem foldl_prefix_eq_full_ringAttn
    (g : GraphDecl) (nodes : List NodeDecl) (s : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ nodes.drop k, n.outs ≠ [])
    (h : ∀ n ∈ nodes.drop k, tid ∉ n.outs) :
    nodes.foldl (applyNodeRingAttn g) s tid =
      (nodes.take k).foldl (applyNodeRingAttn g) s tid := by
  conv_lhs => rw [← List.take_append_drop k nodes, List.foldl_append]
  exact foldl_applyNodeRingAttn_at_not_written g _ _ tid hnil h

/-! ## Stack/gather commutation utilities (graph-independent; copied from legacy Pattern_3). -/

private theorem gather0_2d_valAt
    (numParts Lshard d1 : Nat)
    (Ws : List Tensor)
    (hparts : 0 < numParts) (hL : 0 < Lshard) (hd1 : 0 < d1)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [Lshard, d1])
    (r : Nat) (hr : r < numParts)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1) :
    valAt (allGatherPrimDimN 0 numParts 0 Ws)
          ((r * Lshard + row) * d1 + col) =
      valAt (Ws.getD r (zeroTensor [Lshard, d1]))
            (row * d1 + col) := by
  have hd1_ne : d1 ≠ 0 := Nat.ne_of_gt hd1
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hE_pos : 0 < Lshard * numParts * d1 :=
    Nat.mul_pos (Nat.mul_pos hL hparts) hd1
  have hE_ne : Lshard * numParts * d1 ≠ 0 := Nat.ne_of_gt hE_pos
  have hrr : r * Lshard + row < Lshard * numParts := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ numParts * Lshard := Nat.mul_le_mul_right _ hr
    calc r * Lshard + row < (r + 1) * Lshard := hsi
      _ ≤ numParts * Lshard := hle
      _ = Lshard * numParts := by ring
  have hidx_eq : (r * Lshard + row) * d1 + col
      = col + d1 * (r * Lshard + row) := by ring
  have hidx_lt_E : (r * Lshard + row) * d1 + col < Lshard * numParts * d1 := by
    rw [hidx_eq]
    calc col + d1 * (r * Lshard + row)
        < d1 + d1 * (r * Lshard + row) := by omega
      _ = d1 * (r * Lshard + row + 1) := by ring
      _ ≤ d1 * (Lshard * numParts) := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * numParts * d1 := by ring
  have hdiv_E : ((r * Lshard + row) * d1 + col) / (Lshard * numParts * d1) = 0 :=
    Nat.div_eq_of_lt hidx_lt_E
  have hmod_E : ((r * Lshard + row) * d1 + col) % (Lshard * numParts * d1)
      = (r * Lshard + row) * d1 + col := Nat.mod_eq_of_lt hidx_lt_E
  have hdiv_P : ((r * Lshard + row) * d1 + col) / d1 = r * Lshard + row := by
    rw [hidx_eq, Nat.add_mul_div_left _ _ hd1, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmod_P : ((r * Lshard + row) * d1 + col) % d1 = col := by
    rw [hidx_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  have hdiv_L : (r * Lshard + row) / Lshard = r := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hrow, Nat.zero_add]
  have hmod_L : (r * Lshard + row) % Lshard = row := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have hshape_out : (allGatherPrimDimN 0 numParts 0 Ws).shape
      = [Lshard * numParts, d1] := by
    have := allGatherPrimDimN_shape 0 numParts Ws [Lshard, d1] hhead
    simpa using this
  have hidx_lt_prod : (r * Lshard + row) * d1 + col
      < prodShape (allGatherPrimDimN 0 numParts 0 Ws).shape := by
    rw [hshape_out]
    have hpe : prodShape [Lshard * numParts, d1] = Lshard * numParts * d1 := by
      simp [prodShape, Nat.mul_assoc]
    rw [hpe]; exact hidx_lt_E
  have h0 : valAt (allGatherPrimDimN 0 numParts 0 Ws)
        ((r * Lshard + row) * d1 + col)
      = (allGatherPrimDimN 0 numParts 0 Ws).val
          ⟨(r * Lshard + row) * d1 + col, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    hd1_ne, hL_ne, hE_ne, ite_false]
  rw [hmod_E, hdiv_E, hdiv_P, hmod_P, hdiv_L, hmod_L]
  rw [show 0 * (Lshard * d1) + row * d1 + col
        = row * d1 + col from by ring]

private theorem chunk0_2d_valAt
    (Lshard d1 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1])
    (r : Nat) (hr : r < 2)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1) :
    valAt (chunkPrimDimN 0 2 r T) (row * d1 + col) =
      valAt T ((r * Lshard + row) * d1 + col) := by
  have hd1_ne : d1 ≠ 0 := Nat.ne_of_gt hd1
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hLd_pos : 0 < Lshard * d1 := Nat.mul_pos hL hd1
  have hLd_ne : Lshard * d1 ≠ 0 := Nat.ne_of_gt hLd_pos
  have hloc_eq : row * d1 + col = col + d1 * row := by ring
  have hloc_lt : row * d1 + col < Lshard * d1 := by
    rw [hloc_eq]
    calc col + d1 * row < d1 + d1 * row := by omega
      _ = d1 * (row + 1) := by ring
      _ ≤ d1 * Lshard := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * d1 := by ring
  have hdiv_S : (row * d1 + col) / (Lshard * d1) = 0 := Nat.div_eq_of_lt hloc_lt
  have hmod_S : (row * d1 + col) % (Lshard * d1) = row * d1 + col :=
    Nat.mod_eq_of_lt hloc_lt
  have hdiv_P : (row * d1 + col) / d1 = row := by
    rw [hloc_eq, Nat.add_mul_div_left _ _ hd1, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmod_P : (row * d1 + col) % d1 = col := by
    rw [hloc_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  have hrmod : r % 2 = r := Nat.mod_eq_of_lt hr
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  have hchunk_shape : (chunkPrimDimN 0 2 r T).shape = [Lshard, d1] := by
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [hsh]
  have hloc_lt_prod : row * d1 + col < prodShape (chunkPrimDimN 0 2 r T).shape := by
    rw [hchunk_shape]
    have hpe : prodShape [Lshard, d1] = Lshard * d1 := by simp [prodShape, Nat.mul_assoc]
    rw [hpe]; exact hloc_lt
  rw [valAt_of_lt _ _ hloc_lt_prod]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hT, List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    show ((2:Nat) = 0) = False from by decide, ite_false,
    hsh, hrmod, hd1_ne, hLd_ne]
  rw [hmod_S, hdiv_S, hdiv_P, hmod_P]
  congr 1
  ring

theorem allGather0_reconstruct_chunks_2d
    (Lshard d1 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1]) :
    allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T] = T := by
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  have hc_shape : ∀ r, (chunkPrimDimN 0 2 r T).shape = [Lshard, d1] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]; rw [hsh]
  have hhead : (([chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].head?.map
      (fun t => t.shape)).getD []) = [Lshard, d1] := by simp [hc_shape 0]
  have hgshape : (allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T]).shape
      = [2 * Lshard, d1] := by
    rw [allGatherPrimDimN_shape 0 2 _ [Lshard, d1] hhead]
    simp only [List.set, List.getD_cons_zero]; rw [Nat.mul_comm Lshard 2]
  apply Tensor.ext
  · rw [hgshape, hT]
  · intro idx hidx
    rw [hgshape] at hidx
    have hprod : prodShape [2 * Lshard, d1] = 2 * Lshard * d1 := by
      simp [prodShape, Nat.mul_assoc]
    rw [hprod] at hidx
    set col := idx % d1 with hcol_def
    set fullrow := idx / d1 with hfullrow_def
    have hcol : col < d1 := by rw [hcol_def]; exact Nat.mod_lt _ hd1
    have hfullrow_lt : fullrow < 2 * Lshard := by
      rw [hfullrow_def]
      apply Nat.div_lt_of_lt_mul
      calc idx < 2 * Lshard * d1 := hidx
        _ = d1 * (2 * Lshard) := by ring
    set r := fullrow / Lshard with hr_def
    set row := fullrow % Lshard with hrow_def
    have hrow : row < Lshard := by rw [hrow_def]; exact Nat.mod_lt _ hL
    have hr : r < 2 := by
      rw [hr_def]
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact hfullrow_lt
    have hfullrow_split : fullrow = r * Lshard + row := by
      rw [hr_def, hrow_def]; rw [Nat.mul_comm]; exact (Nat.div_add_mod fullrow Lshard).symm
    have hidx_decomp : idx = (r * Lshard + row) * d1 + col := by
      rw [← hfullrow_split]
      rw [hcol_def, hfullrow_def]
      rw [Nat.mul_comm (idx / d1) d1]
      exact (Nat.div_add_mod idx d1).symm
    rw [hidx_decomp]
    rw [gather0_2d_valAt 2 Lshard d1 _ (by omega) hL hd1 hhead r hr row hrow col hcol]
    have hgetD : [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].getD r (zeroTensor [Lshard, d1])
        = chunkPrimDimN 0 2 r T := by
      interval_cases r <;> rfl
    rw [hgetD]
    exact chunk0_2d_valAt Lshard d1 hL hd1 T hT r hr row hrow col hcol

private theorem allGatherPrimDimN1_of_stack_valAt_2d
    (n Lshard d1 : Nat) (as : List Tensor)
    (_hn : 0 < n) (hL : 0 < Lshard) (hd1 : 0 < d1)
    (hhead : (as.head?.map (fun t => t.shape)).getD [] = [n, Lshard, d1])
    (hshapes : ∀ r (_ : r < 2),
        (as.getD r (zeroTensor [n, Lshard, d1])).shape = [n, Lshard, d1])
    (i : Nat) (hi : i < n)
    (r : Nat) (hr : r < 2)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1) :
    valAt (allGatherPrimDimN 1 2 0 as)
          ((i * (2 * Lshard) + (r * Lshard + row)) * d1 + col) =
      valAt (as.getD r (zeroTensor [n, Lshard, d1]))
            ((i * Lshard + row) * d1 + col) := by
  have hd1_ne : d1 ≠ 0 := Nat.ne_of_gt hd1
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hE_pos : 0 < Lshard * 2 * d1 :=
    Nat.mul_pos (Nat.mul_pos hL (by omega)) hd1
  have hE_ne : Lshard * 2 * d1 ≠ 0 := Nat.ne_of_gt hE_pos
  have hR : r * Lshard + row < 2 * Lshard := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ 2 * Lshard := Nat.mul_le_mul_right _ (by omega)
    exact lt_of_lt_of_le hsi hle
  have hmid_lt : (r * Lshard + row) * d1 + col < Lshard * 2 * d1 := by
    calc (r * Lshard + row) * d1 + col
        < (r * Lshard + row) * d1 + d1 := by omega
      _ = (r * Lshard + row + 1) * d1 := by ring
      _ ≤ (2 * Lshard) * d1 := Nat.mul_le_mul_right _ (by omega)
      _ = Lshard * 2 * d1 := by ring
  have hidx_eq_E :
      (i * (2 * Lshard) + (r * Lshard + row)) * d1 + col
      = ((r * Lshard + row) * d1 + col) + (Lshard * 2 * d1) * i := by ring
  have hdiv_E :
      ((i * (2 * Lshard) + (r * Lshard + row)) * d1 + col) / (Lshard * 2 * d1) = i := by
    rw [hidx_eq_E, Nat.add_mul_div_left _ _ hE_pos, Nat.div_eq_of_lt hmid_lt, Nat.zero_add]
  have hmod_E :
      ((i * (2 * Lshard) + (r * Lshard + row)) * d1 + col) % (Lshard * 2 * d1)
      = (r * Lshard + row) * d1 + col := by
    rw [hidx_eq_E, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmid_lt]
  have hM_eq : (r * Lshard + row) * d1 + col
      = col + d1 * (r * Lshard + row) := by ring
  have hdiv_P : ((r * Lshard + row) * d1 + col) / d1 = r * Lshard + row := by
    rw [hM_eq, Nat.add_mul_div_left _ _ hd1, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmod_P : ((r * Lshard + row) * d1 + col) % d1 = col := by
    rw [hM_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  have hdiv_L : (r * Lshard + row) / Lshard = r := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hrow, Nat.zero_add]
  have hmod_L : (r * Lshard + row) % Lshard = row := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have hshape_out : (allGatherPrimDimN 1 2 0 as).shape = [n, Lshard * 2, d1] := by
    have := allGatherPrimDimN_shape 1 2 as [n, Lshard, d1] hhead
    simpa [List.set] using this
  have hidx_lt_prod :
      (i * (2 * Lshard) + (r * Lshard + row)) * d1 + col
      < prodShape (allGatherPrimDimN 1 2 0 as).shape := by
    rw [hshape_out]
    have hpe : prodShape [n, Lshard * 2, d1] = n * (Lshard * 2 * d1) := by
      simp [prodShape]; ring
    rw [hpe, hidx_eq_E]
    calc ((r * Lshard + row) * d1 + col) + (Lshard * 2 * d1) * i
        < (Lshard * 2 * d1) + (Lshard * 2 * d1) * i := by omega
      _ = (Lshard * 2 * d1) * (i + 1) := by ring
      _ ≤ (Lshard * 2 * d1) * n := Nat.mul_le_mul_left _ (by omega)
      _ = n * (Lshard * 2 * d1) := by ring
  have har_shape : (as.getD r (zeroTensor [n, Lshard, d1])).shape = [n, Lshard, d1] :=
    hshapes r hr
  have har_prod : prodShape (as.getD r (zeroTensor [n, Lshard, d1])).shape
      = n * (Lshard * d1) := by
    rw [har_shape]; simp [prodShape]; ring
  have hidx_lt_ar : (i * Lshard + row) * d1 + col
      < prodShape (as.getD r (zeroTensor [n, Lshard, d1])).shape := by
    rw [har_prod]
    have hrowlow : row * d1 + col < Lshard * d1 := by
      calc row * d1 + col < row * d1 + d1 := by omega
        _ = (row + 1) * d1 := by ring
        _ ≤ Lshard * d1 := Nat.mul_le_mul_right _ (by omega)
    calc (i * Lshard + row) * d1 + col
        = (Lshard * d1) * i + (row * d1 + col) := by ring
      _ < (Lshard * d1) * i + Lshard * d1 := by omega
      _ = (Lshard * d1) * (i + 1) := by ring
      _ ≤ (Lshard * d1) * n := Nat.mul_le_mul_left _ (by omega)
      _ = n * (Lshard * d1) := by ring
  have h0 : valAt (allGatherPrimDimN 1 2 0 as)
        ((i * (2 * Lshard) + (r * Lshard + row)) * d1 + col)
      = (allGatherPrimDimN 1 2 0 as).val
          ⟨(i * (2 * Lshard) + (r * Lshard + row)) * d1 + col, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD_cons_succ, List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    hd1_ne, hL_ne, hE_ne, ite_false]
  rw [hmod_E, hdiv_E, hdiv_P, hmod_P, hdiv_L, hmod_L]
  rw [show i * (Lshard * d1) + row * d1 + col
        = (i * Lshard + row) * d1 + col from by ring]

theorem fw_stack_allGather0_dim1_commute_2d_element
    (n Lshard d1 : Nat)
    (hL : 0 < Lshard) (hd1 : 0 < d1)
    (xs ys zs : List Tensor)
    (hxlen : xs.length = n) (hylen : ys.length = n) (hzlen : zs.length = n)
    (hxhead : (xs.head?.map (fun t => t.shape)).getD [] = [Lshard, d1])
    (hyhead : (ys.head?.map (fun t => t.shape)).getD [] = [Lshard, d1])
    (hzhead : (zs.head?.map (fun t => t.shape)).getD [] = [2 * Lshard, d1])
    (hxshapes : ∀ i (_ : i < n),
      (xs.getD i (zeroTensor [Lshard, d1])).shape = [Lshard, d1])
    (hyshapes : ∀ i (_ : i < n),
      (ys.getD i (zeroTensor [Lshard, d1])).shape = [Lshard, d1])
    (hcommute : ∀ i (_ : i < n),
      zs.getD i (zeroTensor [2 * Lshard, d1]) =
      allGatherPrimDimN 0 2 0
        [xs.getD i (zeroTensor [Lshard, d1]),
         ys.getD i (zeroTensor [Lshard, d1])]) :
    fw_stack zs =
      allGatherPrimDimN 1 2 0 [fw_stack xs, fw_stack ys] := by
  have hLHS_shape : (fw_stack zs).shape = [n, 2 * Lshard, d1] := by
    have := fw_stack_shape zs [2 * Lshard, d1] hzhead; rw [hzlen] at this; exact this
  have hxstack_shape : (fw_stack xs).shape = [n, Lshard, d1] := by
    have := fw_stack_shape xs [Lshard, d1] hxhead; rw [hxlen] at this; exact this
  have hystack_shape : (fw_stack ys).shape = [n, Lshard, d1] := by
    have := fw_stack_shape ys [Lshard, d1] hyhead; rw [hylen] at this; exact this
  have hhead2 : (([fw_stack xs, fw_stack ys].head?.map (fun t => t.shape)).getD [])
      = [n, Lshard, d1] := by simp [hxstack_shape]
  have hRHS_shape : (allGatherPrimDimN 1 2 0 [fw_stack xs, fw_stack ys]).shape
      = [n, 2 * Lshard, d1] := by
    rw [allGatherPrimDimN_shape 1 2 _ [n, Lshard, d1] hhead2]
    simp only [List.set, List.getD_cons_succ, List.getD_cons_zero]
    rw [Nat.mul_comm Lshard 2]
  have hprod : prodShape [n, 2 * Lshard, d1] = n * (2 * Lshard) * d1 := by
    simp [prodShape]
  have hps3 : prodShape [2 * Lshard, d1] = 2 * Lshard * d1 := by simp [prodShape]
  have hps3xy : prodShape [Lshard, d1] = Lshard * d1 := by simp [prodShape]
  have hzshard_pos : 0 < prodShape [2 * Lshard, d1] := by rw [hps3]; positivity
  have hxyshard_pos : 0 < prodShape [Lshard, d1] := by rw [hps3xy]; positivity
  have hshapes2 : ∀ r (_ : r < 2),
      ([fw_stack xs, fw_stack ys].getD r (zeroTensor [n, Lshard, d1])).shape
        = [n, Lshard, d1] := by
    intro r hr; interval_cases r
    · simpa [List.getD] using hxstack_shape
    · simpa [List.getD] using hystack_shape
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro flatIdx hflat
    rw [hLHS_shape] at hflat
    rw [hprod] at hflat
    set col := flatIdx % d1 with hcol_def
    set row := (flatIdx / d1) % (2 * Lshard) with hrow_def
    set i := flatIdx / d1 / (2 * Lshard) with hi_def
    have hcol : col < d1 := by rw [hcol_def]; exact Nat.mod_lt _ hd1
    have hrow : row < 2 * Lshard := by rw [hrow_def]; exact Nat.mod_lt _ (by omega)
    have hi : i < n := by
      rw [hi_def]
      apply Nat.div_lt_of_lt_mul
      apply Nat.div_lt_of_lt_mul
      calc flatIdx < n * (2 * Lshard) * d1 := hflat
        _ = d1 * (2 * Lshard * n) := by ring
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hi
    have hL1 : flatIdx = d1 * (flatIdx / d1) + col := by
      rw [hcol_def]; exact (Nat.div_add_mod flatIdx d1).symm
    have hL0 : flatIdx / d1 = (2 * Lshard) * i + row := by
      rw [hrow_def, hi_def]; exact (Nat.div_add_mod (flatIdx / d1) (2 * Lshard)).symm
    have hdecomp : flatIdx = (i * (2 * Lshard) + row) * d1 + col := by
      rw [hL1, hL0]; ring
    have hlocal : (row * d1 + col) < prodShape [2 * Lshard, d1] := by
      rw [hps3]
      calc row * d1 + col = d1 * row + col := by ring
        _ < d1 * row + d1 := by omega
        _ = d1 * (row + 1) := by ring
        _ ≤ d1 * (2 * Lshard) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * Lshard * d1 := by ring
    have hbnd : ∀ w, w < Lshard → w * d1 + col < prodShape [Lshard, d1] := by
      intro w hw; rw [hps3xy]
      calc w * d1 + col = d1 * w + col := by ring
        _ < d1 * w + d1 := by omega
        _ = d1 * (w + 1) := by ring
        _ ≤ d1 * Lshard := Nat.mul_le_mul_left _ (by omega)
        _ = Lshard * d1 := by ring
    have hxi_shape : (xs.getD i (zeroTensor [Lshard, d1])).shape = [Lshard, d1] :=
      hxshapes i hi
    have hyi_shape : (ys.getD i (zeroTensor [Lshard, d1])).shape = [Lshard, d1] :=
      hyshapes i hi
    have hhead_inner : (([xs.getD i (zeroTensor [Lshard, d1]),
          ys.getD i (zeroTensor [Lshard, d1])].head?.map (fun t => t.shape)).getD [])
        = [Lshard, d1] := by
      simp only [List.head?, Option.map, Option.getD]; exact hxi_shape
    rw [hdecomp]
    conv_lhs => rw [show (i * (2 * Lshard) + row) * d1 + col
        = i * prodShape [2 * Lshard, d1] + (row * d1 + col)
        from by rw [hps3]; ring]
    rw [fw_stack_valAt zs [2 * Lshard, d1] hzhead hzshard_pos i
        (by rw [hzlen]; exact hi) (row * d1 + col) hlocal]
    rw [hcommute i hi]
    by_cases hrl : row < Lshard
    · conv_lhs => rw [show row * d1 + col
          = (0 * Lshard + row) * d1 + col from by ring]
      rw [gather0_2d_valAt 2 Lshard d1
          [xs.getD i (zeroTensor [Lshard, d1]), ys.getD i (zeroTensor [Lshard, d1])]
          (by omega) hL hd1 hhead_inner 0 (by omega) row hrl col hcol]
      conv_rhs => rw [show (i * (2 * Lshard) + row) * d1 + col
          = (i * (2 * Lshard) + (0 * Lshard + row)) * d1 + col from by ring]
      rw [allGatherPrimDimN1_of_stack_valAt_2d n Lshard d1 [fw_stack xs, fw_stack ys]
          hnpos hL hd1 hhead2 hshapes2 i hi 0 (by omega) row hrl col hcol]
      simp only [List.getD_cons_zero]
      rw [show (i * Lshard + row) * d1 + col
          = i * prodShape [Lshard, d1] + (row * d1 + col)
          from by rw [hps3xy]; ring]
      rw [fw_stack_valAt xs [Lshard, d1] hxhead hxyshard_pos i
          (by rw [hxlen]; exact hi) (row * d1 + col) (hbnd row hrl)]
    · have hrsub : row - Lshard < Lshard := by omega
      conv_lhs => rw [show row * d1 + col
          = (1 * Lshard + (row - Lshard)) * d1 + col
          from by rw [show 1 * Lshard + (row - Lshard) = row from by omega]]
      rw [gather0_2d_valAt 2 Lshard d1
          [xs.getD i (zeroTensor [Lshard, d1]), ys.getD i (zeroTensor [Lshard, d1])]
          (by omega) hL hd1 hhead_inner 1 (by omega) (row - Lshard) hrsub col hcol]
      conv_rhs => rw [show (i * (2 * Lshard) + row) * d1 + col
          = (i * (2 * Lshard) + (1 * Lshard + (row - Lshard))) * d1 + col
          from by rw [show 1 * Lshard + (row - Lshard) = row from by omega]]
      rw [allGatherPrimDimN1_of_stack_valAt_2d n Lshard d1 [fw_stack xs, fw_stack ys]
          hnpos hL hd1 hhead2 hshapes2 i hi 1 (by omega)
          (row - Lshard) hrsub col hcol]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [show (i * Lshard + (row - Lshard)) * d1 + col
          = i * prodShape [Lshard, d1] + ((row - Lshard) * d1 + col)
          from by rw [hps3xy]; ring]
      rw [fw_stack_valAt ys [Lshard, d1] hyhead hxyshard_pos i
          (by rw [hylen]; exact hi) ((row - Lshard) * d1 + col) (hbnd _ hrsub)]



/-! ## Faithful per-layer router output lists. -/

noncomputable def sm_goal_3_faithful_routers (initSM : Store) : List Tensor := [denoteGraph_ringAttn sm_goal_3_faithful initSM 4710, denoteGraph_ringAttn sm_goal_3_faithful initSM 4764, denoteGraph_ringAttn sm_goal_3_faithful initSM 4818, denoteGraph_ringAttn sm_goal_3_faithful initSM 4872, denoteGraph_ringAttn sm_goal_3_faithful initSM 4926, denoteGraph_ringAttn sm_goal_3_faithful initSM 4980, denoteGraph_ringAttn sm_goal_3_faithful initSM 5034, denoteGraph_ringAttn sm_goal_3_faithful initSM 5088, denoteGraph_ringAttn sm_goal_3_faithful initSM 5142, denoteGraph_ringAttn sm_goal_3_faithful initSM 5196, denoteGraph_ringAttn sm_goal_3_faithful initSM 5250, denoteGraph_ringAttn sm_goal_3_faithful initSM 5304, denoteGraph_ringAttn sm_goal_3_faithful initSM 5361, denoteGraph_ringAttn sm_goal_3_faithful initSM 5410, denoteGraph_ringAttn sm_goal_3_faithful initSM 5459, denoteGraph_ringAttn sm_goal_3_faithful initSM 5508, denoteGraph_ringAttn sm_goal_3_faithful initSM 5557, denoteGraph_ringAttn sm_goal_3_faithful initSM 5606, denoteGraph_ringAttn sm_goal_3_faithful initSM 5655, denoteGraph_ringAttn sm_goal_3_faithful initSM 5704, denoteGraph_ringAttn sm_goal_3_faithful initSM 5753, denoteGraph_ringAttn sm_goal_3_faithful initSM 5802, denoteGraph_ringAttn sm_goal_3_faithful initSM 5851, denoteGraph_ringAttn sm_goal_3_faithful initSM 5900]
noncomputable def pm_goal_3_faithful_routers_r0 (initPM : Store) : List Tensor := [denoteGraph_ringAttn pm_goal_3_faithful initPM 7483, denoteGraph_ringAttn pm_goal_3_faithful initPM 7669, denoteGraph_ringAttn pm_goal_3_faithful initPM 7855, denoteGraph_ringAttn pm_goal_3_faithful initPM 8041, denoteGraph_ringAttn pm_goal_3_faithful initPM 8227, denoteGraph_ringAttn pm_goal_3_faithful initPM 8413, denoteGraph_ringAttn pm_goal_3_faithful initPM 8599, denoteGraph_ringAttn pm_goal_3_faithful initPM 8785, denoteGraph_ringAttn pm_goal_3_faithful initPM 8971, denoteGraph_ringAttn pm_goal_3_faithful initPM 9157, denoteGraph_ringAttn pm_goal_3_faithful initPM 9343, denoteGraph_ringAttn pm_goal_3_faithful initPM 9529, denoteGraph_ringAttn pm_goal_3_faithful initPM 9733, denoteGraph_ringAttn pm_goal_3_faithful initPM 9905, denoteGraph_ringAttn pm_goal_3_faithful initPM 10077, denoteGraph_ringAttn pm_goal_3_faithful initPM 10249, denoteGraph_ringAttn pm_goal_3_faithful initPM 10421, denoteGraph_ringAttn pm_goal_3_faithful initPM 10593, denoteGraph_ringAttn pm_goal_3_faithful initPM 10765, denoteGraph_ringAttn pm_goal_3_faithful initPM 10937, denoteGraph_ringAttn pm_goal_3_faithful initPM 11109, denoteGraph_ringAttn pm_goal_3_faithful initPM 11281, denoteGraph_ringAttn pm_goal_3_faithful initPM 11453, denoteGraph_ringAttn pm_goal_3_faithful initPM 11625]
noncomputable def pm_goal_3_faithful_routers_r1 (initPM : Store) : List Tensor := [denoteGraph_ringAttn pm_goal_3_faithful initPM 7484, denoteGraph_ringAttn pm_goal_3_faithful initPM 7670, denoteGraph_ringAttn pm_goal_3_faithful initPM 7856, denoteGraph_ringAttn pm_goal_3_faithful initPM 8042, denoteGraph_ringAttn pm_goal_3_faithful initPM 8228, denoteGraph_ringAttn pm_goal_3_faithful initPM 8414, denoteGraph_ringAttn pm_goal_3_faithful initPM 8600, denoteGraph_ringAttn pm_goal_3_faithful initPM 8786, denoteGraph_ringAttn pm_goal_3_faithful initPM 8972, denoteGraph_ringAttn pm_goal_3_faithful initPM 9158, denoteGraph_ringAttn pm_goal_3_faithful initPM 9344, denoteGraph_ringAttn pm_goal_3_faithful initPM 9530, denoteGraph_ringAttn pm_goal_3_faithful initPM 9734, denoteGraph_ringAttn pm_goal_3_faithful initPM 9906, denoteGraph_ringAttn pm_goal_3_faithful initPM 10078, denoteGraph_ringAttn pm_goal_3_faithful initPM 10250, denoteGraph_ringAttn pm_goal_3_faithful initPM 10422, denoteGraph_ringAttn pm_goal_3_faithful initPM 10594, denoteGraph_ringAttn pm_goal_3_faithful initPM 10766, denoteGraph_ringAttn pm_goal_3_faithful initPM 10938, denoteGraph_ringAttn pm_goal_3_faithful initPM 11110, denoteGraph_ringAttn pm_goal_3_faithful initPM 11282, denoteGraph_ringAttn pm_goal_3_faithful initPM 11454, denoteGraph_ringAttn pm_goal_3_faithful initPM 11626]


/-! ## Faithful unfold helpers for the final stack/allGather assembly. -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in

theorem denote_sm_goal_3_faithful_4675 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4675 =
      (fw_stack [(denoteGraph_ringAttn sm_goal_3_faithful initSM 4710), (denoteGraph_ringAttn sm_goal_3_faithful initSM 4764), (denoteGraph_ringAttn sm_goal_3_faithful initSM 4818), (denoteGraph_ringAttn sm_goal_3_faithful initSM 4872), (denoteGraph_ringAttn sm_goal_3_faithful initSM 4926), (denoteGraph_ringAttn sm_goal_3_faithful initSM 4980), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5034), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5088), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5142), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5196), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5250), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5304), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5361), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5410), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5459), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5508), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5557), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5606), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5655), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5704), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5753), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5802), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5851), (denoteGraph_ringAttn sm_goal_3_faithful initSM 5900)]) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4675 =
      (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4675 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4675 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4675 850 (by decide) (by decide)
  rw [hEntry]
  rw [show sm_goal_3_faithful.nodes.take 850 = sm_goal_3_faithful.nodes.take 849 ++ [{ rank := 0, op := "OpName.FW_stack", ins := [4710, 4764, 4818, 4872, 4926, 4980, 5034, 5088, 5142, 5196, 5250, 5304, 5361, 5410, 5459, 5508, 5557, 5606, 5655, 5704, 5753, 5802, 5851, 5900], outs := [4675] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 849).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_stack", ins := [4710, 4764, 4818, 4872, 4926, 4980, 5034, 5088, 5142, 5196, 5250, 5304, 5361, 5410, 5459, 5508, 5557, 5606, 5655, 5704, 5753, 5802, 5851, 5900], outs := [4675] } (by decide) (by decide)]
  rw [applyNode_fw_stack_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 849).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 [4710, 4764, 4818, 4872, 4926, 4980, 5034, 5088, 5142, 5196, 5250, 5304, 5361, 5410, 5459, 5508, 5557, 5606, 5655, 5704, 5753, 5802, 5851, 5900] 4675 []]
  simp only [List.map_cons, List.map_nil]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4710 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4764 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4818 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4872 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4926 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4980 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5034 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5088 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5142 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5196 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5250 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5304 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5361 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5410 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5459 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5508 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5557 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5606 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5655 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5704 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5753 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5802 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5851 849 850 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5900 849 850 (by omega) (by decide) (by decide)]
  have hval_5900 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5900 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5900 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5900 850 (by decide) (by decide)).symm
  have hval_5851 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5851 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5851 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5851 850 (by decide) (by decide)).symm
  have hval_5802 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5802 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5802 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5802 850 (by decide) (by decide)).symm
  have hval_5753 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5753 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5753 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5753 850 (by decide) (by decide)).symm
  have hval_5704 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5704 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5704 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5704 850 (by decide) (by decide)).symm
  have hval_5655 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5655 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5655 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5655 850 (by decide) (by decide)).symm
  have hval_5606 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5606 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5606 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5606 850 (by decide) (by decide)).symm
  have hval_5557 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5557 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5557 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5557 850 (by decide) (by decide)).symm
  have hval_5508 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5508 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5508 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5508 850 (by decide) (by decide)).symm
  have hval_5459 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5459 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5459 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5459 850 (by decide) (by decide)).symm
  have hval_5410 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5410 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5410 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5410 850 (by decide) (by decide)).symm
  have hval_5361 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5361 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5361 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5361 850 (by decide) (by decide)).symm
  have hval_5304 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5304 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5304 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5304 850 (by decide) (by decide)).symm
  have hval_5250 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5250 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5250 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5250 850 (by decide) (by decide)).symm
  have hval_5196 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5196 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5196 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5196 850 (by decide) (by decide)).symm
  have hval_5142 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5142 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5142 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5142 850 (by decide) (by decide)).symm
  have hval_5088 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5088 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5088 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5088 850 (by decide) (by decide)).symm
  have hval_5034 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5034 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5034 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5034 850 (by decide) (by decide)).symm
  have hval_4980 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4980 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4980 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4980 850 (by decide) (by decide)).symm
  have hval_4926 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4926 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4926 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4926 850 (by decide) (by decide)).symm
  have hval_4872 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4872 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4872 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4872 850 (by decide) (by decide)).symm
  have hval_4818 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4818 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4818 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4818 850 (by decide) (by decide)).symm
  have hval_4764 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4764 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4764 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4764 850 (by decide) (by decide)).symm
  have hval_4710 : (((sm_goal_3_faithful.nodes.take 850).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4710 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4710 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4710 850 (by decide) (by decide)).symm
  rw [hval_5900, hval_5851, hval_5802, hval_5753, hval_5704, hval_5655, hval_5606, hval_5557, hval_5508, hval_5459, hval_5410, hval_5361, hval_5304, hval_5250, hval_5196, hval_5142, hval_5088, hval_5034, hval_4980, hval_4926, hval_4872, hval_4818, hval_4764, hval_4710]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_stack_r0 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 11729 =
      (fw_stack [(denoteGraph_ringAttn pm_goal_3_faithful initPM 7483), (denoteGraph_ringAttn pm_goal_3_faithful initPM 7669), (denoteGraph_ringAttn pm_goal_3_faithful initPM 7855), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8041), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8227), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8413), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8599), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8785), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8971), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9157), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9343), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9529), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9733), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9905), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10077), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10249), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10421), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10593), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10765), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10937), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11109), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11281), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11453), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11625)]) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 11729 =
      (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11729 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 11729 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11729 1857 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 1857 = pm_goal_3_faithful.nodes.take 1856 ++ [{ rank := 0, op := "OpName.FW_stack", ins := [7483, 7669, 7855, 8041, 8227, 8413, 8599, 8785, 8971, 9157, 9343, 9529, 9733, 9905, 10077, 10249, 10421, 10593, 10765, 10937, 11109, 11281, 11453, 11625], outs := [11729] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1856).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_stack", ins := [7483, 7669, 7855, 8041, 8227, 8413, 8599, 8785, 8971, 9157, 9343, 9529, 9733, 9905, 10077, 10249, 10421, 10593, 10765, 10937, 11109, 11281, 11453, 11625], outs := [11729] } (by decide) (by decide)]
  rw [applyNode_fw_stack_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1856).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 [7483, 7669, 7855, 8041, 8227, 8413, 8599, 8785, 8971, 9157, 9343, 9529, 9733, 9905, 10077, 10249, 10421, 10593, 10765, 10937, 11109, 11281, 11453, 11625] 11729 []]
  simp only [List.map_cons, List.map_nil]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7483 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7669 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7855 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8041 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8227 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8413 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8599 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8785 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8971 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9157 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9343 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9529 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9733 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9905 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10077 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10249 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10421 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10593 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10765 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10937 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11109 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11281 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11453 1856 1857 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11625 1856 1857 (by omega) (by decide) (by decide)]
  have hval_11625 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11625 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11625 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11625 1857 (by decide) (by decide)).symm
  have hval_11453 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11453 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11453 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11453 1857 (by decide) (by decide)).symm
  have hval_11281 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11281 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11281 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11281 1857 (by decide) (by decide)).symm
  have hval_11109 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11109 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11109 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11109 1857 (by decide) (by decide)).symm
  have hval_10937 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10937 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10937 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10937 1857 (by decide) (by decide)).symm
  have hval_10765 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10765 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10765 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10765 1857 (by decide) (by decide)).symm
  have hval_10593 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10593 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10593 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10593 1857 (by decide) (by decide)).symm
  have hval_10421 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10421 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10421 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10421 1857 (by decide) (by decide)).symm
  have hval_10249 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10249 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10249 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10249 1857 (by decide) (by decide)).symm
  have hval_10077 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10077 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10077 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10077 1857 (by decide) (by decide)).symm
  have hval_9905 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9905 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9905 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9905 1857 (by decide) (by decide)).symm
  have hval_9733 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9733 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9733 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9733 1857 (by decide) (by decide)).symm
  have hval_9529 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9529 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9529 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9529 1857 (by decide) (by decide)).symm
  have hval_9343 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9343 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9343 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9343 1857 (by decide) (by decide)).symm
  have hval_9157 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9157 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9157 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9157 1857 (by decide) (by decide)).symm
  have hval_8971 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8971 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8971 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8971 1857 (by decide) (by decide)).symm
  have hval_8785 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8785 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8785 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8785 1857 (by decide) (by decide)).symm
  have hval_8599 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8599 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8599 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8599 1857 (by decide) (by decide)).symm
  have hval_8413 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8413 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8413 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8413 1857 (by decide) (by decide)).symm
  have hval_8227 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8227 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8227 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8227 1857 (by decide) (by decide)).symm
  have hval_8041 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8041 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8041 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8041 1857 (by decide) (by decide)).symm
  have hval_7855 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7855 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7855 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7855 1857 (by decide) (by decide)).symm
  have hval_7669 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7669 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7669 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7669 1857 (by decide) (by decide)).symm
  have hval_7483 : (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7483 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7483 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7483 1857 (by decide) (by decide)).symm
  rw [hval_11625, hval_11453, hval_11281, hval_11109, hval_10937, hval_10765, hval_10593, hval_10421, hval_10249, hval_10077, hval_9905, hval_9733, hval_9529, hval_9343, hval_9157, hval_8971, hval_8785, hval_8599, hval_8413, hval_8227, hval_8041, hval_7855, hval_7669, hval_7483]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_stack_r1 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 11730 =
      (fw_stack [(denoteGraph_ringAttn pm_goal_3_faithful initPM 7484), (denoteGraph_ringAttn pm_goal_3_faithful initPM 7670), (denoteGraph_ringAttn pm_goal_3_faithful initPM 7856), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8042), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8228), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8414), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8600), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8786), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8972), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9158), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9344), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9530), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9734), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9906), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10078), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10250), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10422), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10594), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10766), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10938), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11110), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11282), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11454), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11626)]) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 11730 =
      (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11730 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 11730 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11730 1858 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 1858 = pm_goal_3_faithful.nodes.take 1857 ++ [{ rank := 1, op := "OpName.FW_stack", ins := [7484, 7670, 7856, 8042, 8228, 8414, 8600, 8786, 8972, 9158, 9344, 9530, 9734, 9906, 10078, 10250, 10422, 10594, 10766, 10938, 11110, 11282, 11454, 11626], outs := [11730] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_stack", ins := [7484, 7670, 7856, 8042, 8228, 8414, 8600, 8786, 8972, 9158, 9344, 9530, 9734, 9906, 10078, 10250, 10422, 10594, 10766, 10938, 11110, 11282, 11454, 11626], outs := [11730] } (by decide) (by decide)]
  rw [applyNode_fw_stack_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1857).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 [7484, 7670, 7856, 8042, 8228, 8414, 8600, 8786, 8972, 9158, 9344, 9530, 9734, 9906, 10078, 10250, 10422, 10594, 10766, 10938, 11110, 11282, 11454, 11626] 11730 []]
  simp only [List.map_cons, List.map_nil]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7484 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7670 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7856 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8042 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8228 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8414 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8600 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8786 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8972 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9158 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9344 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9530 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9734 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9906 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10078 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10250 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10422 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10594 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10766 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10938 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11110 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11282 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11454 1857 1858 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11626 1857 1858 (by omega) (by decide) (by decide)]
  have hval_11626 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11626 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11626 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11626 1858 (by decide) (by decide)).symm
  have hval_11454 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11454 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11454 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11454 1858 (by decide) (by decide)).symm
  have hval_11282 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11282 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11282 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11282 1858 (by decide) (by decide)).symm
  have hval_11110 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11110 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11110 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11110 1858 (by decide) (by decide)).symm
  have hval_10938 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10938 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10938 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10938 1858 (by decide) (by decide)).symm
  have hval_10766 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10766 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10766 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10766 1858 (by decide) (by decide)).symm
  have hval_10594 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10594 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10594 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10594 1858 (by decide) (by decide)).symm
  have hval_10422 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10422 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10422 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10422 1858 (by decide) (by decide)).symm
  have hval_10250 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10250 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10250 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10250 1858 (by decide) (by decide)).symm
  have hval_10078 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10078 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10078 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10078 1858 (by decide) (by decide)).symm
  have hval_9906 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9906 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9906 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9906 1858 (by decide) (by decide)).symm
  have hval_9734 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9734 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9734 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9734 1858 (by decide) (by decide)).symm
  have hval_9530 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9530 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9530 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9530 1858 (by decide) (by decide)).symm
  have hval_9344 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9344 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9344 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9344 1858 (by decide) (by decide)).symm
  have hval_9158 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9158 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9158 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9158 1858 (by decide) (by decide)).symm
  have hval_8972 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8972 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8972 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8972 1858 (by decide) (by decide)).symm
  have hval_8786 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8786 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8786 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8786 1858 (by decide) (by decide)).symm
  have hval_8600 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8600 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8600 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8600 1858 (by decide) (by decide)).symm
  have hval_8414 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8414 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8414 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8414 1858 (by decide) (by decide)).symm
  have hval_8228 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8228 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8228 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8228 1858 (by decide) (by decide)).symm
  have hval_8042 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8042 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8042 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8042 1858 (by decide) (by decide)).symm
  have hval_7856 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7856 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7856 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7856 1858 (by decide) (by decide)).symm
  have hval_7670 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7670 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7670 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7670 1858 (by decide) (by decide)).symm
  have hval_7484 : (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7484 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7484 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7484 1858 (by decide) (by decide)).symm
  rw [hval_11626, hval_11454, hval_11282, hval_11110, hval_10938, hval_10766, hval_10594, hval_10422, hval_10250, hval_10078, hval_9906, hval_9734, hval_9530, hval_9344, hval_9158, hval_8972, hval_8786, hval_8600, hval_8414, hval_8228, hval_8042, hval_7856, hval_7670, hval_7484]
  try rfl

theorem denote_pm_goal_3_faithful_4675 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 4675 =
      (allGatherPrimDimN 1 pm_goal_3_faithful.numRanks 0 [(denoteGraph_ringAttn pm_goal_3_faithful initPM 11729), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11730)]) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 4675 =
      (((pm_goal_3_faithful.nodes.take 1859).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4675 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4675 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4675 1859 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 1859 = pm_goal_3_faithful.nodes.take 1858 ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [11729, 11730], outs := [4675], params := [1] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.AllGatherPrim", ins := [11729, 11730], outs := [4675], params := [1] } (by decide) (by decide)]
  rw [applyNode_allGatherPrimDimN_out_thm pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1858).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 [11729, 11730] 4675 1]
  simp only [List.map_cons, List.map_nil]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11729 1858 1859 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11730 1858 1859 (by omega) (by decide) (by decide)]
  have hval_11730 : (((pm_goal_3_faithful.nodes.take 1859).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11730 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11730 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11730 1859 (by decide) (by decide)).symm
  have hval_11729 : (((pm_goal_3_faithful.nodes.take 1859).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11729 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11729 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11729 1859 (by decide) (by decide)).symm
  rw [hval_11730, hval_11729]
  try rfl


/-! ## Final-stack reduction: reduces goal_3 to the 24 per-layer router commutes. -/

set_option maxHeartbeats 8000000 in
theorem goal_3_stmt_cut_ringAttn_of_router_commutes
    (H : ∀ (initSM initPM : Store),
        StoreShapesHold initSM sm_goal_3_faithfulInitEnv →
        StoreShapesHold initPM pm_goal_3_faithfulInitEnv →
        InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM →
        (∀ i (_ : i < 24), ((pm_goal_3_faithful_routers_r0 initPM).getD i (zeroTensor [2048, 64])).shape = [2048, 64]) ∧
        (∀ i (_ : i < 24), ((pm_goal_3_faithful_routers_r1 initPM).getD i (zeroTensor [2048, 64])).shape = [2048, 64]) ∧
        (∀ i (_ : i < 24), (sm_goal_3_faithful_routers initSM).getD i (zeroTensor [2 * 2048, 64]) =
          allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful_routers_r0 initPM).getD i (zeroTensor [2048, 64]),
            (pm_goal_3_faithful_routers_r1 initPM).getD i (zeroTensor [2048, 64])])) :
    goal_3_stmt_cut_ringAttn := by
  unfold goal_3_stmt_cut_ringAttn CoarseLineageHoldsWithInit_ringAttn
  intro initSM initPM hSM hPM hInit
  obtain ⟨hxshapes, hyshapes, hcommute⟩ := H initSM initPM hSM hPM hInit
  simp only [sm_goal_3_faithful_routers, pm_goal_3_faithful_routers_r0, pm_goal_3_faithful_routers_r1] at hxshapes hyshapes hcommute
  have hxhead : ((([denoteGraph_ringAttn pm_goal_3_faithful initPM 7483, denoteGraph_ringAttn pm_goal_3_faithful initPM 7669, denoteGraph_ringAttn pm_goal_3_faithful initPM 7855, denoteGraph_ringAttn pm_goal_3_faithful initPM 8041, denoteGraph_ringAttn pm_goal_3_faithful initPM 8227, denoteGraph_ringAttn pm_goal_3_faithful initPM 8413, denoteGraph_ringAttn pm_goal_3_faithful initPM 8599, denoteGraph_ringAttn pm_goal_3_faithful initPM 8785, denoteGraph_ringAttn pm_goal_3_faithful initPM 8971, denoteGraph_ringAttn pm_goal_3_faithful initPM 9157, denoteGraph_ringAttn pm_goal_3_faithful initPM 9343, denoteGraph_ringAttn pm_goal_3_faithful initPM 9529, denoteGraph_ringAttn pm_goal_3_faithful initPM 9733, denoteGraph_ringAttn pm_goal_3_faithful initPM 9905, denoteGraph_ringAttn pm_goal_3_faithful initPM 10077, denoteGraph_ringAttn pm_goal_3_faithful initPM 10249, denoteGraph_ringAttn pm_goal_3_faithful initPM 10421, denoteGraph_ringAttn pm_goal_3_faithful initPM 10593, denoteGraph_ringAttn pm_goal_3_faithful initPM 10765, denoteGraph_ringAttn pm_goal_3_faithful initPM 10937, denoteGraph_ringAttn pm_goal_3_faithful initPM 11109, denoteGraph_ringAttn pm_goal_3_faithful initPM 11281, denoteGraph_ringAttn pm_goal_3_faithful initPM 11453, denoteGraph_ringAttn pm_goal_3_faithful initPM 11625] : List Tensor).head?.map (fun t => t.shape)).getD []) = [2048, 64] := by
    have := hxshapes 0 (by norm_num); simpa using this
  have hyhead : ((([denoteGraph_ringAttn pm_goal_3_faithful initPM 7484, denoteGraph_ringAttn pm_goal_3_faithful initPM 7670, denoteGraph_ringAttn pm_goal_3_faithful initPM 7856, denoteGraph_ringAttn pm_goal_3_faithful initPM 8042, denoteGraph_ringAttn pm_goal_3_faithful initPM 8228, denoteGraph_ringAttn pm_goal_3_faithful initPM 8414, denoteGraph_ringAttn pm_goal_3_faithful initPM 8600, denoteGraph_ringAttn pm_goal_3_faithful initPM 8786, denoteGraph_ringAttn pm_goal_3_faithful initPM 8972, denoteGraph_ringAttn pm_goal_3_faithful initPM 9158, denoteGraph_ringAttn pm_goal_3_faithful initPM 9344, denoteGraph_ringAttn pm_goal_3_faithful initPM 9530, denoteGraph_ringAttn pm_goal_3_faithful initPM 9734, denoteGraph_ringAttn pm_goal_3_faithful initPM 9906, denoteGraph_ringAttn pm_goal_3_faithful initPM 10078, denoteGraph_ringAttn pm_goal_3_faithful initPM 10250, denoteGraph_ringAttn pm_goal_3_faithful initPM 10422, denoteGraph_ringAttn pm_goal_3_faithful initPM 10594, denoteGraph_ringAttn pm_goal_3_faithful initPM 10766, denoteGraph_ringAttn pm_goal_3_faithful initPM 10938, denoteGraph_ringAttn pm_goal_3_faithful initPM 11110, denoteGraph_ringAttn pm_goal_3_faithful initPM 11282, denoteGraph_ringAttn pm_goal_3_faithful initPM 11454, denoteGraph_ringAttn pm_goal_3_faithful initPM 11626] : List Tensor).head?.map (fun t => t.shape)).getD []) = [2048, 64] := by
    have := hyshapes 0 (by norm_num); simpa using this
  have hzhead : ((([denoteGraph_ringAttn sm_goal_3_faithful initSM 4710, denoteGraph_ringAttn sm_goal_3_faithful initSM 4764, denoteGraph_ringAttn sm_goal_3_faithful initSM 4818, denoteGraph_ringAttn sm_goal_3_faithful initSM 4872, denoteGraph_ringAttn sm_goal_3_faithful initSM 4926, denoteGraph_ringAttn sm_goal_3_faithful initSM 4980, denoteGraph_ringAttn sm_goal_3_faithful initSM 5034, denoteGraph_ringAttn sm_goal_3_faithful initSM 5088, denoteGraph_ringAttn sm_goal_3_faithful initSM 5142, denoteGraph_ringAttn sm_goal_3_faithful initSM 5196, denoteGraph_ringAttn sm_goal_3_faithful initSM 5250, denoteGraph_ringAttn sm_goal_3_faithful initSM 5304, denoteGraph_ringAttn sm_goal_3_faithful initSM 5361, denoteGraph_ringAttn sm_goal_3_faithful initSM 5410, denoteGraph_ringAttn sm_goal_3_faithful initSM 5459, denoteGraph_ringAttn sm_goal_3_faithful initSM 5508, denoteGraph_ringAttn sm_goal_3_faithful initSM 5557, denoteGraph_ringAttn sm_goal_3_faithful initSM 5606, denoteGraph_ringAttn sm_goal_3_faithful initSM 5655, denoteGraph_ringAttn sm_goal_3_faithful initSM 5704, denoteGraph_ringAttn sm_goal_3_faithful initSM 5753, denoteGraph_ringAttn sm_goal_3_faithful initSM 5802, denoteGraph_ringAttn sm_goal_3_faithful initSM 5851, denoteGraph_ringAttn sm_goal_3_faithful initSM 5900] : List Tensor).head?.map (fun t => t.shape)).getD []) = [2 * 2048, 64] := by
    have h0 := hcommute 0 (by norm_num)
    have hx0 := hxshapes 0 (by norm_num)
    have hy0 := hyshapes 0 (by norm_num)
    simp only [List.getD_cons_zero] at h0 hx0 hy0
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    rw [h0]
    have hhd : (([denoteGraph_ringAttn pm_goal_3_faithful initPM 7483, denoteGraph_ringAttn pm_goal_3_faithful initPM 7484] : List Tensor).head?.map (fun t => t.shape)).getD [] = [2048, 64] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]; exact hx0
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhd]
    simp only [List.set, List.getD_cons_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp only [goal_3]
    rw [denote_sm_goal_3_faithful_4675 initSM]
    have hfs := fw_stack_shape ([denoteGraph_ringAttn sm_goal_3_faithful initSM 4710, denoteGraph_ringAttn sm_goal_3_faithful initSM 4764, denoteGraph_ringAttn sm_goal_3_faithful initSM 4818, denoteGraph_ringAttn sm_goal_3_faithful initSM 4872, denoteGraph_ringAttn sm_goal_3_faithful initSM 4926, denoteGraph_ringAttn sm_goal_3_faithful initSM 4980, denoteGraph_ringAttn sm_goal_3_faithful initSM 5034, denoteGraph_ringAttn sm_goal_3_faithful initSM 5088, denoteGraph_ringAttn sm_goal_3_faithful initSM 5142, denoteGraph_ringAttn sm_goal_3_faithful initSM 5196, denoteGraph_ringAttn sm_goal_3_faithful initSM 5250, denoteGraph_ringAttn sm_goal_3_faithful initSM 5304, denoteGraph_ringAttn sm_goal_3_faithful initSM 5361, denoteGraph_ringAttn sm_goal_3_faithful initSM 5410, denoteGraph_ringAttn sm_goal_3_faithful initSM 5459, denoteGraph_ringAttn sm_goal_3_faithful initSM 5508, denoteGraph_ringAttn sm_goal_3_faithful initSM 5557, denoteGraph_ringAttn sm_goal_3_faithful initSM 5606, denoteGraph_ringAttn sm_goal_3_faithful initSM 5655, denoteGraph_ringAttn sm_goal_3_faithful initSM 5704, denoteGraph_ringAttn sm_goal_3_faithful initSM 5753, denoteGraph_ringAttn sm_goal_3_faithful initSM 5802, denoteGraph_ringAttn sm_goal_3_faithful initSM 5851, denoteGraph_ringAttn sm_goal_3_faithful initSM 5900] : List Tensor) [4096, 64] (by simpa using hzhead)
    rw [hfs]; norm_num
  · simp only [goal_3, List.map_cons, List.map_nil]
    rw [denote_pm_goal_3_faithful_4675 initPM, denote_pm_goal_3_faithful_stack_r0 initPM, denote_pm_goal_3_faithful_stack_r1 initPM]
    have hnr : pm_goal_3_faithful.numRanks = 2 := rfl
    rw [hnr]
    have hstack0 : (fw_stack ([denoteGraph_ringAttn pm_goal_3_faithful initPM 7483, denoteGraph_ringAttn pm_goal_3_faithful initPM 7669, denoteGraph_ringAttn pm_goal_3_faithful initPM 7855, denoteGraph_ringAttn pm_goal_3_faithful initPM 8041, denoteGraph_ringAttn pm_goal_3_faithful initPM 8227, denoteGraph_ringAttn pm_goal_3_faithful initPM 8413, denoteGraph_ringAttn pm_goal_3_faithful initPM 8599, denoteGraph_ringAttn pm_goal_3_faithful initPM 8785, denoteGraph_ringAttn pm_goal_3_faithful initPM 8971, denoteGraph_ringAttn pm_goal_3_faithful initPM 9157, denoteGraph_ringAttn pm_goal_3_faithful initPM 9343, denoteGraph_ringAttn pm_goal_3_faithful initPM 9529, denoteGraph_ringAttn pm_goal_3_faithful initPM 9733, denoteGraph_ringAttn pm_goal_3_faithful initPM 9905, denoteGraph_ringAttn pm_goal_3_faithful initPM 10077, denoteGraph_ringAttn pm_goal_3_faithful initPM 10249, denoteGraph_ringAttn pm_goal_3_faithful initPM 10421, denoteGraph_ringAttn pm_goal_3_faithful initPM 10593, denoteGraph_ringAttn pm_goal_3_faithful initPM 10765, denoteGraph_ringAttn pm_goal_3_faithful initPM 10937, denoteGraph_ringAttn pm_goal_3_faithful initPM 11109, denoteGraph_ringAttn pm_goal_3_faithful initPM 11281, denoteGraph_ringAttn pm_goal_3_faithful initPM 11453, denoteGraph_ringAttn pm_goal_3_faithful initPM 11625] : List Tensor)).shape = [24, 2048, 64] := by
      have hfs := fw_stack_shape ([denoteGraph_ringAttn pm_goal_3_faithful initPM 7483, denoteGraph_ringAttn pm_goal_3_faithful initPM 7669, denoteGraph_ringAttn pm_goal_3_faithful initPM 7855, denoteGraph_ringAttn pm_goal_3_faithful initPM 8041, denoteGraph_ringAttn pm_goal_3_faithful initPM 8227, denoteGraph_ringAttn pm_goal_3_faithful initPM 8413, denoteGraph_ringAttn pm_goal_3_faithful initPM 8599, denoteGraph_ringAttn pm_goal_3_faithful initPM 8785, denoteGraph_ringAttn pm_goal_3_faithful initPM 8971, denoteGraph_ringAttn pm_goal_3_faithful initPM 9157, denoteGraph_ringAttn pm_goal_3_faithful initPM 9343, denoteGraph_ringAttn pm_goal_3_faithful initPM 9529, denoteGraph_ringAttn pm_goal_3_faithful initPM 9733, denoteGraph_ringAttn pm_goal_3_faithful initPM 9905, denoteGraph_ringAttn pm_goal_3_faithful initPM 10077, denoteGraph_ringAttn pm_goal_3_faithful initPM 10249, denoteGraph_ringAttn pm_goal_3_faithful initPM 10421, denoteGraph_ringAttn pm_goal_3_faithful initPM 10593, denoteGraph_ringAttn pm_goal_3_faithful initPM 10765, denoteGraph_ringAttn pm_goal_3_faithful initPM 10937, denoteGraph_ringAttn pm_goal_3_faithful initPM 11109, denoteGraph_ringAttn pm_goal_3_faithful initPM 11281, denoteGraph_ringAttn pm_goal_3_faithful initPM 11453, denoteGraph_ringAttn pm_goal_3_faithful initPM 11625] : List Tensor) [2048, 64] hxhead; rw [hfs]; norm_num
    have hstackhead : (([fw_stack ([denoteGraph_ringAttn pm_goal_3_faithful initPM 7483, denoteGraph_ringAttn pm_goal_3_faithful initPM 7669, denoteGraph_ringAttn pm_goal_3_faithful initPM 7855, denoteGraph_ringAttn pm_goal_3_faithful initPM 8041, denoteGraph_ringAttn pm_goal_3_faithful initPM 8227, denoteGraph_ringAttn pm_goal_3_faithful initPM 8413, denoteGraph_ringAttn pm_goal_3_faithful initPM 8599, denoteGraph_ringAttn pm_goal_3_faithful initPM 8785, denoteGraph_ringAttn pm_goal_3_faithful initPM 8971, denoteGraph_ringAttn pm_goal_3_faithful initPM 9157, denoteGraph_ringAttn pm_goal_3_faithful initPM 9343, denoteGraph_ringAttn pm_goal_3_faithful initPM 9529, denoteGraph_ringAttn pm_goal_3_faithful initPM 9733, denoteGraph_ringAttn pm_goal_3_faithful initPM 9905, denoteGraph_ringAttn pm_goal_3_faithful initPM 10077, denoteGraph_ringAttn pm_goal_3_faithful initPM 10249, denoteGraph_ringAttn pm_goal_3_faithful initPM 10421, denoteGraph_ringAttn pm_goal_3_faithful initPM 10593, denoteGraph_ringAttn pm_goal_3_faithful initPM 10765, denoteGraph_ringAttn pm_goal_3_faithful initPM 10937, denoteGraph_ringAttn pm_goal_3_faithful initPM 11109, denoteGraph_ringAttn pm_goal_3_faithful initPM 11281, denoteGraph_ringAttn pm_goal_3_faithful initPM 11453, denoteGraph_ringAttn pm_goal_3_faithful initPM 11625] : List Tensor), fw_stack ([denoteGraph_ringAttn pm_goal_3_faithful initPM 7484, denoteGraph_ringAttn pm_goal_3_faithful initPM 7670, denoteGraph_ringAttn pm_goal_3_faithful initPM 7856, denoteGraph_ringAttn pm_goal_3_faithful initPM 8042, denoteGraph_ringAttn pm_goal_3_faithful initPM 8228, denoteGraph_ringAttn pm_goal_3_faithful initPM 8414, denoteGraph_ringAttn pm_goal_3_faithful initPM 8600, denoteGraph_ringAttn pm_goal_3_faithful initPM 8786, denoteGraph_ringAttn pm_goal_3_faithful initPM 8972, denoteGraph_ringAttn pm_goal_3_faithful initPM 9158, denoteGraph_ringAttn pm_goal_3_faithful initPM 9344, denoteGraph_ringAttn pm_goal_3_faithful initPM 9530, denoteGraph_ringAttn pm_goal_3_faithful initPM 9734, denoteGraph_ringAttn pm_goal_3_faithful initPM 9906, denoteGraph_ringAttn pm_goal_3_faithful initPM 10078, denoteGraph_ringAttn pm_goal_3_faithful initPM 10250, denoteGraph_ringAttn pm_goal_3_faithful initPM 10422, denoteGraph_ringAttn pm_goal_3_faithful initPM 10594, denoteGraph_ringAttn pm_goal_3_faithful initPM 10766, denoteGraph_ringAttn pm_goal_3_faithful initPM 10938, denoteGraph_ringAttn pm_goal_3_faithful initPM 11110, denoteGraph_ringAttn pm_goal_3_faithful initPM 11282, denoteGraph_ringAttn pm_goal_3_faithful initPM 11454, denoteGraph_ringAttn pm_goal_3_faithful initPM 11626] : List Tensor)].head?.map (fun t => t.shape)).getD []) = [24, 2048, 64] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]; exact hstack0
    rw [allGatherPrimDimN_shape 1 2 _ [24, 2048, 64] hstackhead]
    norm_num [List.set]
  · simp only [goal_3, List.map_cons, List.map_nil, reconstructWithDim_singleton]
    rw [denote_sm_goal_3_faithful_4675 initSM, denote_pm_goal_3_faithful_4675 initPM, denote_pm_goal_3_faithful_stack_r0 initPM, denote_pm_goal_3_faithful_stack_r1 initPM]
    have hnr : pm_goal_3_faithful.numRanks = 2 := rfl
    rw [hnr]
    exact fw_stack_allGather0_dim1_commute_2d_element 24 2048 64 (by norm_num) (by norm_num)
      ([denoteGraph_ringAttn pm_goal_3_faithful initPM 7483, denoteGraph_ringAttn pm_goal_3_faithful initPM 7669, denoteGraph_ringAttn pm_goal_3_faithful initPM 7855, denoteGraph_ringAttn pm_goal_3_faithful initPM 8041, denoteGraph_ringAttn pm_goal_3_faithful initPM 8227, denoteGraph_ringAttn pm_goal_3_faithful initPM 8413, denoteGraph_ringAttn pm_goal_3_faithful initPM 8599, denoteGraph_ringAttn pm_goal_3_faithful initPM 8785, denoteGraph_ringAttn pm_goal_3_faithful initPM 8971, denoteGraph_ringAttn pm_goal_3_faithful initPM 9157, denoteGraph_ringAttn pm_goal_3_faithful initPM 9343, denoteGraph_ringAttn pm_goal_3_faithful initPM 9529, denoteGraph_ringAttn pm_goal_3_faithful initPM 9733, denoteGraph_ringAttn pm_goal_3_faithful initPM 9905, denoteGraph_ringAttn pm_goal_3_faithful initPM 10077, denoteGraph_ringAttn pm_goal_3_faithful initPM 10249, denoteGraph_ringAttn pm_goal_3_faithful initPM 10421, denoteGraph_ringAttn pm_goal_3_faithful initPM 10593, denoteGraph_ringAttn pm_goal_3_faithful initPM 10765, denoteGraph_ringAttn pm_goal_3_faithful initPM 10937, denoteGraph_ringAttn pm_goal_3_faithful initPM 11109, denoteGraph_ringAttn pm_goal_3_faithful initPM 11281, denoteGraph_ringAttn pm_goal_3_faithful initPM 11453, denoteGraph_ringAttn pm_goal_3_faithful initPM 11625] : List Tensor)
      ([denoteGraph_ringAttn pm_goal_3_faithful initPM 7484, denoteGraph_ringAttn pm_goal_3_faithful initPM 7670, denoteGraph_ringAttn pm_goal_3_faithful initPM 7856, denoteGraph_ringAttn pm_goal_3_faithful initPM 8042, denoteGraph_ringAttn pm_goal_3_faithful initPM 8228, denoteGraph_ringAttn pm_goal_3_faithful initPM 8414, denoteGraph_ringAttn pm_goal_3_faithful initPM 8600, denoteGraph_ringAttn pm_goal_3_faithful initPM 8786, denoteGraph_ringAttn pm_goal_3_faithful initPM 8972, denoteGraph_ringAttn pm_goal_3_faithful initPM 9158, denoteGraph_ringAttn pm_goal_3_faithful initPM 9344, denoteGraph_ringAttn pm_goal_3_faithful initPM 9530, denoteGraph_ringAttn pm_goal_3_faithful initPM 9734, denoteGraph_ringAttn pm_goal_3_faithful initPM 9906, denoteGraph_ringAttn pm_goal_3_faithful initPM 10078, denoteGraph_ringAttn pm_goal_3_faithful initPM 10250, denoteGraph_ringAttn pm_goal_3_faithful initPM 10422, denoteGraph_ringAttn pm_goal_3_faithful initPM 10594, denoteGraph_ringAttn pm_goal_3_faithful initPM 10766, denoteGraph_ringAttn pm_goal_3_faithful initPM 10938, denoteGraph_ringAttn pm_goal_3_faithful initPM 11110, denoteGraph_ringAttn pm_goal_3_faithful initPM 11282, denoteGraph_ringAttn pm_goal_3_faithful initPM 11454, denoteGraph_ringAttn pm_goal_3_faithful initPM 11626] : List Tensor)
      ([denoteGraph_ringAttn sm_goal_3_faithful initSM 4710, denoteGraph_ringAttn sm_goal_3_faithful initSM 4764, denoteGraph_ringAttn sm_goal_3_faithful initSM 4818, denoteGraph_ringAttn sm_goal_3_faithful initSM 4872, denoteGraph_ringAttn sm_goal_3_faithful initSM 4926, denoteGraph_ringAttn sm_goal_3_faithful initSM 4980, denoteGraph_ringAttn sm_goal_3_faithful initSM 5034, denoteGraph_ringAttn sm_goal_3_faithful initSM 5088, denoteGraph_ringAttn sm_goal_3_faithful initSM 5142, denoteGraph_ringAttn sm_goal_3_faithful initSM 5196, denoteGraph_ringAttn sm_goal_3_faithful initSM 5250, denoteGraph_ringAttn sm_goal_3_faithful initSM 5304, denoteGraph_ringAttn sm_goal_3_faithful initSM 5361, denoteGraph_ringAttn sm_goal_3_faithful initSM 5410, denoteGraph_ringAttn sm_goal_3_faithful initSM 5459, denoteGraph_ringAttn sm_goal_3_faithful initSM 5508, denoteGraph_ringAttn sm_goal_3_faithful initSM 5557, denoteGraph_ringAttn sm_goal_3_faithful initSM 5606, denoteGraph_ringAttn sm_goal_3_faithful initSM 5655, denoteGraph_ringAttn sm_goal_3_faithful initSM 5704, denoteGraph_ringAttn sm_goal_3_faithful initSM 5753, denoteGraph_ringAttn sm_goal_3_faithful initSM 5802, denoteGraph_ringAttn sm_goal_3_faithful initSM 5851, denoteGraph_ringAttn sm_goal_3_faithful initSM 5900] : List Tensor)
      (by norm_num) (by norm_num) (by norm_num)
      hxhead hyhead hzhead hxshapes hyshapes hcommute


/-! ## Sub-obligations — 24 layer router commutes, isolated per layer.

    Each `sm_pm_router_commute_L{k}` is a self-contained lemma for layer k.
    Batch workers each own one file / one lemma. Once ALL 24 are proved,
    `sm_pm_router_commute_all` assembles them by `Fin.cases`.

    ALSO isolated: `sm_pm_router_shapes_r0`/`r1` cover the 24 shape claims
    per rank. Under the faithful reshape semantics these are 24 shape-
    reduction chains through fw_view / fw_linear / fw_add / rms_norm /
    per_head_mix_precision_linear / attn — routine but bulky. -/

/-- pm rank-0 router shapes at every layer. Discharged by
    `Pattern_3_faithful_RouterShapes.lean` (Worker A). -/
theorem sm_pm_router_shapes_r0
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    ∀ i (_ : i < 24), ((pm_goal_3_faithful_routers_r0 initPM).getD i (zeroTensor [2048, 64])).shape = [2048, 64] := by
  sorry

/-- pm rank-1 router shapes at every layer. Same file as `_r0`. -/
theorem sm_pm_router_shapes_r1
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    ∀ i (_ : i < 24), ((pm_goal_3_faithful_routers_r1 initPM).getD i (zeroTensor [2048, 64])).shape = [2048, 64] := by
  sorry

/-- Per-layer commute (`sm.router_L{k} = allGather0 [pm_r0.router_L{k}, pm_r1.router_L{k}]`).
    L0..L11 use sliding_window attn (shard-local, causal window = 512 ≤ 2048).
    L12..L23 use zigzag ring attn (cross-rank q-gather + broadcast k/v).
    Under the faithful reshape semantics these are all TRUE and provable per
    the schema in `PROMPT.md`. -/
theorem sm_pm_router_commute_layer
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    ∀ i (_ : i < 24),
      (sm_goal_3_faithful_routers initSM).getD i (zeroTensor [2 * 2048, 64]) =
        allGatherPrimDimN 0 2 0
          [(pm_goal_3_faithful_routers_r0 initPM).getD i (zeroTensor [2048, 64]),
           (pm_goal_3_faithful_routers_r1 initPM).getD i (zeroTensor [2048, 64])] := by
  sorry

/-- Assembly of the three components. Kernel-clean once the three above are. -/
theorem sm_pm_router_commute_all
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    (∀ i (_ : i < 24), ((pm_goal_3_faithful_routers_r0 initPM).getD i (zeroTensor [2048, 64])).shape = [2048, 64]) ∧
    (∀ i (_ : i < 24), ((pm_goal_3_faithful_routers_r1 initPM).getD i (zeroTensor [2048, 64])).shape = [2048, 64]) ∧
    (∀ i (_ : i < 24), (sm_goal_3_faithful_routers initSM).getD i (zeroTensor [2 * 2048, 64]) =
      allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful_routers_r0 initPM).getD i (zeroTensor [2048, 64]),
        (pm_goal_3_faithful_routers_r1 initPM).getD i (zeroTensor [2048, 64])]) :=
  ⟨sm_pm_router_shapes_r0 initSM initPM hSM hPM hInit,
   sm_pm_router_shapes_r1 initSM initPM hSM hPM hInit,
   sm_pm_router_commute_layer initSM initPM hSM hPM hInit⟩


/-- Top-level Pattern_3 proof under the faithful reshape semantics.
    Reduced (kernel-clean) to the single `sm_pm_router_commute_all` obligation. -/
theorem prove_goal_3 : goal_3_stmt_cut_ringAttn :=
  goal_3_stmt_cut_ringAttn_of_router_commutes
    (fun initSM initPM hSM hPM hInit => sm_pm_router_commute_all initSM initPM hSM hPM hInit)

/-- Pattern 3 discharge (in the faithful variant). Mirrors the old pattern_3_target
    binding used in MainTheorem.lean; we bind to the goal_3_stmt_cut_ringAttn Prop
    from Goal_3_faithful namespace. -/
def pattern_3_target : Prop := goal_3_stmt_cut_ringAttn

theorem prove_pattern_3 : pattern_3_target := prove_goal_3

end TrainVerify.Denote.Pattern3Faithful
