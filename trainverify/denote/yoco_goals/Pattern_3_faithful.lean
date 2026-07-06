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
      (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4675 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4675 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4675 903 (by decide) (by decide)
  rw [hEntry]
  rw [show sm_goal_3_faithful.nodes.take 903 = sm_goal_3_faithful.nodes.take 902 ++ [{ rank := 0, op := "OpName.FW_stack", ins := [4710, 4764, 4818, 4872, 4926, 4980, 5034, 5088, 5142, 5196, 5250, 5304, 5361, 5410, 5459, 5508, 5557, 5606, 5655, 5704, 5753, 5802, 5851, 5900], outs := [4675] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 902).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_stack", ins := [4710, 4764, 4818, 4872, 4926, 4980, 5034, 5088, 5142, 5196, 5250, 5304, 5361, 5410, 5459, 5508, 5557, 5606, 5655, 5704, 5753, 5802, 5851, 5900], outs := [4675] } (by decide) (by decide)]
  rw [applyNode_fw_stack_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 902).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 [4710, 4764, 4818, 4872, 4926, 4980, 5034, 5088, 5142, 5196, 5250, 5304, 5361, 5410, 5459, 5508, 5557, 5606, 5655, 5704, 5753, 5802, 5851, 5900] 4675 []]
  simp only [List.map_cons, List.map_nil]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4710 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4764 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4818 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4872 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4926 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4980 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5034 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5088 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5142 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5196 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5250 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5304 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5361 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5410 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5459 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5508 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5557 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5606 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5655 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5704 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5753 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5802 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5851 902 903 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5900 902 903 (by omega) (by decide) (by decide)]
  have hval_5900 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5900 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5900 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5900 903 (by decide) (by decide)).symm
  have hval_5851 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5851 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5851 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5851 903 (by decide) (by decide)).symm
  have hval_5802 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5802 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5802 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5802 903 (by decide) (by decide)).symm
  have hval_5753 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5753 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5753 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5753 903 (by decide) (by decide)).symm
  have hval_5704 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5704 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5704 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5704 903 (by decide) (by decide)).symm
  have hval_5655 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5655 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5655 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5655 903 (by decide) (by decide)).symm
  have hval_5606 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5606 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5606 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5606 903 (by decide) (by decide)).symm
  have hval_5557 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5557 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5557 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5557 903 (by decide) (by decide)).symm
  have hval_5508 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5508 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5508 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5508 903 (by decide) (by decide)).symm
  have hval_5459 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5459 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5459 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5459 903 (by decide) (by decide)).symm
  have hval_5410 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5410 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5410 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5410 903 (by decide) (by decide)).symm
  have hval_5361 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5361 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5361 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5361 903 (by decide) (by decide)).symm
  have hval_5304 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5304 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5304 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5304 903 (by decide) (by decide)).symm
  have hval_5250 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5250 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5250 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5250 903 (by decide) (by decide)).symm
  have hval_5196 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5196 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5196 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5196 903 (by decide) (by decide)).symm
  have hval_5142 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5142 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5142 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5142 903 (by decide) (by decide)).symm
  have hval_5088 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5088 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5088 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5088 903 (by decide) (by decide)).symm
  have hval_5034 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 5034 = denoteGraph_ringAttn sm_goal_3_faithful initSM 5034 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 5034 903 (by decide) (by decide)).symm
  have hval_4980 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4980 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4980 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4980 903 (by decide) (by decide)).symm
  have hval_4926 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4926 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4926 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4926 903 (by decide) (by decide)).symm
  have hval_4872 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4872 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4872 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4872 903 (by decide) (by decide)).symm
  have hval_4818 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4818 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4818 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4818 903 (by decide) (by decide)).symm
  have hval_4764 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4764 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4764 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4764 903 (by decide) (by decide)).symm
  have hval_4710 : (((sm_goal_3_faithful.nodes.take 903).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4710 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4710 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4710 903 (by decide) (by decide)).symm
  rw [hval_5900, hval_5851, hval_5802, hval_5753, hval_5704, hval_5655, hval_5606, hval_5557, hval_5508, hval_5459, hval_5410, hval_5361, hval_5304, hval_5250, hval_5196, hval_5142, hval_5088, hval_5034, hval_4980, hval_4926, hval_4872, hval_4818, hval_4764, hval_4710]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_stack_r0 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 11729 =
      (fw_stack [(denoteGraph_ringAttn pm_goal_3_faithful initPM 7483), (denoteGraph_ringAttn pm_goal_3_faithful initPM 7669), (denoteGraph_ringAttn pm_goal_3_faithful initPM 7855), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8041), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8227), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8413), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8599), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8785), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8971), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9157), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9343), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9529), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9733), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9905), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10077), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10249), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10421), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10593), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10765), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10937), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11109), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11281), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11453), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11625)]) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 11729 =
      (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11729 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 11729 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11729 1864 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 1864 = pm_goal_3_faithful.nodes.take 1863 ++ [{ rank := 0, op := "OpName.FW_stack", ins := [7483, 7669, 7855, 8041, 8227, 8413, 8599, 8785, 8971, 9157, 9343, 9529, 9733, 9905, 10077, 10249, 10421, 10593, 10765, 10937, 11109, 11281, 11453, 11625], outs := [11729] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1863).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_stack", ins := [7483, 7669, 7855, 8041, 8227, 8413, 8599, 8785, 8971, 9157, 9343, 9529, 9733, 9905, 10077, 10249, 10421, 10593, 10765, 10937, 11109, 11281, 11453, 11625], outs := [11729] } (by decide) (by decide)]
  rw [applyNode_fw_stack_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1863).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 [7483, 7669, 7855, 8041, 8227, 8413, 8599, 8785, 8971, 9157, 9343, 9529, 9733, 9905, 10077, 10249, 10421, 10593, 10765, 10937, 11109, 11281, 11453, 11625] 11729 []]
  simp only [List.map_cons, List.map_nil]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7483 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7669 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7855 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8041 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8227 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8413 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8599 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8785 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8971 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9157 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9343 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9529 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9733 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9905 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10077 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10249 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10421 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10593 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10765 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10937 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11109 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11281 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11453 1863 1864 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11625 1863 1864 (by omega) (by decide) (by decide)]
  have hval_11625 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11625 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11625 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11625 1864 (by decide) (by decide)).symm
  have hval_11453 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11453 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11453 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11453 1864 (by decide) (by decide)).symm
  have hval_11281 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11281 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11281 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11281 1864 (by decide) (by decide)).symm
  have hval_11109 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11109 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11109 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11109 1864 (by decide) (by decide)).symm
  have hval_10937 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10937 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10937 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10937 1864 (by decide) (by decide)).symm
  have hval_10765 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10765 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10765 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10765 1864 (by decide) (by decide)).symm
  have hval_10593 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10593 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10593 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10593 1864 (by decide) (by decide)).symm
  have hval_10421 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10421 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10421 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10421 1864 (by decide) (by decide)).symm
  have hval_10249 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10249 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10249 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10249 1864 (by decide) (by decide)).symm
  have hval_10077 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10077 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10077 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10077 1864 (by decide) (by decide)).symm
  have hval_9905 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9905 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9905 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9905 1864 (by decide) (by decide)).symm
  have hval_9733 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9733 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9733 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9733 1864 (by decide) (by decide)).symm
  have hval_9529 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9529 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9529 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9529 1864 (by decide) (by decide)).symm
  have hval_9343 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9343 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9343 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9343 1864 (by decide) (by decide)).symm
  have hval_9157 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9157 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9157 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9157 1864 (by decide) (by decide)).symm
  have hval_8971 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8971 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8971 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8971 1864 (by decide) (by decide)).symm
  have hval_8785 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8785 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8785 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8785 1864 (by decide) (by decide)).symm
  have hval_8599 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8599 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8599 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8599 1864 (by decide) (by decide)).symm
  have hval_8413 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8413 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8413 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8413 1864 (by decide) (by decide)).symm
  have hval_8227 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8227 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8227 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8227 1864 (by decide) (by decide)).symm
  have hval_8041 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8041 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8041 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8041 1864 (by decide) (by decide)).symm
  have hval_7855 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7855 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7855 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7855 1864 (by decide) (by decide)).symm
  have hval_7669 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7669 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7669 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7669 1864 (by decide) (by decide)).symm
  have hval_7483 : (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7483 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7483 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7483 1864 (by decide) (by decide)).symm
  rw [hval_11625, hval_11453, hval_11281, hval_11109, hval_10937, hval_10765, hval_10593, hval_10421, hval_10249, hval_10077, hval_9905, hval_9733, hval_9529, hval_9343, hval_9157, hval_8971, hval_8785, hval_8599, hval_8413, hval_8227, hval_8041, hval_7855, hval_7669, hval_7483]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_stack_r1 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 11730 =
      (fw_stack [(denoteGraph_ringAttn pm_goal_3_faithful initPM 7484), (denoteGraph_ringAttn pm_goal_3_faithful initPM 7670), (denoteGraph_ringAttn pm_goal_3_faithful initPM 7856), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8042), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8228), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8414), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8600), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8786), (denoteGraph_ringAttn pm_goal_3_faithful initPM 8972), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9158), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9344), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9530), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9734), (denoteGraph_ringAttn pm_goal_3_faithful initPM 9906), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10078), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10250), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10422), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10594), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10766), (denoteGraph_ringAttn pm_goal_3_faithful initPM 10938), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11110), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11282), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11454), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11626)]) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 11730 =
      (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11730 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 11730 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11730 1865 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 1865 = pm_goal_3_faithful.nodes.take 1864 ++ [{ rank := 1, op := "OpName.FW_stack", ins := [7484, 7670, 7856, 8042, 8228, 8414, 8600, 8786, 8972, 9158, 9344, 9530, 9734, 9906, 10078, 10250, 10422, 10594, 10766, 10938, 11110, 11282, 11454, 11626], outs := [11730] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_stack", ins := [7484, 7670, 7856, 8042, 8228, 8414, 8600, 8786, 8972, 9158, 9344, 9530, 9734, 9906, 10078, 10250, 10422, 10594, 10766, 10938, 11110, 11282, 11454, 11626], outs := [11730] } (by decide) (by decide)]
  rw [applyNode_fw_stack_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1864).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 [7484, 7670, 7856, 8042, 8228, 8414, 8600, 8786, 8972, 9158, 9344, 9530, 9734, 9906, 10078, 10250, 10422, 10594, 10766, 10938, 11110, 11282, 11454, 11626] 11730 []]
  simp only [List.map_cons, List.map_nil]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7484 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7670 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7856 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8042 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8228 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8414 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8600 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8786 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8972 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9158 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9344 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9530 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9734 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9906 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10078 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10250 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10422 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10594 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10766 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10938 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11110 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11282 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11454 1864 1865 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11626 1864 1865 (by omega) (by decide) (by decide)]
  have hval_11626 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11626 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11626 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11626 1865 (by decide) (by decide)).symm
  have hval_11454 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11454 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11454 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11454 1865 (by decide) (by decide)).symm
  have hval_11282 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11282 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11282 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11282 1865 (by decide) (by decide)).symm
  have hval_11110 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11110 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11110 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11110 1865 (by decide) (by decide)).symm
  have hval_10938 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10938 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10938 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10938 1865 (by decide) (by decide)).symm
  have hval_10766 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10766 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10766 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10766 1865 (by decide) (by decide)).symm
  have hval_10594 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10594 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10594 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10594 1865 (by decide) (by decide)).symm
  have hval_10422 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10422 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10422 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10422 1865 (by decide) (by decide)).symm
  have hval_10250 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10250 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10250 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10250 1865 (by decide) (by decide)).symm
  have hval_10078 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 10078 = denoteGraph_ringAttn pm_goal_3_faithful initPM 10078 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 10078 1865 (by decide) (by decide)).symm
  have hval_9906 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9906 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9906 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9906 1865 (by decide) (by decide)).symm
  have hval_9734 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9734 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9734 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9734 1865 (by decide) (by decide)).symm
  have hval_9530 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9530 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9530 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9530 1865 (by decide) (by decide)).symm
  have hval_9344 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9344 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9344 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9344 1865 (by decide) (by decide)).symm
  have hval_9158 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 9158 = denoteGraph_ringAttn pm_goal_3_faithful initPM 9158 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 9158 1865 (by decide) (by decide)).symm
  have hval_8972 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8972 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8972 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8972 1865 (by decide) (by decide)).symm
  have hval_8786 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8786 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8786 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8786 1865 (by decide) (by decide)).symm
  have hval_8600 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8600 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8600 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8600 1865 (by decide) (by decide)).symm
  have hval_8414 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8414 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8414 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8414 1865 (by decide) (by decide)).symm
  have hval_8228 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8228 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8228 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8228 1865 (by decide) (by decide)).symm
  have hval_8042 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 8042 = denoteGraph_ringAttn pm_goal_3_faithful initPM 8042 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 8042 1865 (by decide) (by decide)).symm
  have hval_7856 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7856 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7856 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7856 1865 (by decide) (by decide)).symm
  have hval_7670 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7670 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7670 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7670 1865 (by decide) (by decide)).symm
  have hval_7484 : (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7484 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7484 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7484 1865 (by decide) (by decide)).symm
  rw [hval_11626, hval_11454, hval_11282, hval_11110, hval_10938, hval_10766, hval_10594, hval_10422, hval_10250, hval_10078, hval_9906, hval_9734, hval_9530, hval_9344, hval_9158, hval_8972, hval_8786, hval_8600, hval_8414, hval_8228, hval_8042, hval_7856, hval_7670, hval_7484]
  try rfl

theorem denote_pm_goal_3_faithful_4675 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 4675 =
      (allGatherPrimDimN 1 pm_goal_3_faithful.numRanks 0 [(denoteGraph_ringAttn pm_goal_3_faithful initPM 11729), (denoteGraph_ringAttn pm_goal_3_faithful initPM 11730)]) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 4675 =
      (((pm_goal_3_faithful.nodes.take 1866).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4675 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4675 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4675 1866 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 1866 = pm_goal_3_faithful.nodes.take 1865 ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [11729, 11730], outs := [4675], params := [1] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.AllGatherPrim", ins := [11729, 11730], outs := [4675], params := [1] } (by decide) (by decide)]
  rw [applyNode_allGatherPrimDimN_out_thm pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 1865).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 [11729, 11730] 4675 1]
  simp only [List.map_cons, List.map_nil]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11729 1865 1866 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11730 1865 1866 (by omega) (by decide) (by decide)]
  have hval_11730 : (((pm_goal_3_faithful.nodes.take 1866).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11730 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11730 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11730 1866 (by decide) (by decide)).symm
  have hval_11729 : (((pm_goal_3_faithful.nodes.take 1866).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11729 = denoteGraph_ringAttn pm_goal_3_faithful initPM 11729 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11729 1866 (by decide) (by decide)).symm
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

/-- **Reusable router-split reduction (kernel-clean, all 24 layers).**

    The heart of the per-layer router commute. Suppose the SM full norm-linear
    logits tensor `NL_SM` equals the PM full norm-linear logits tensor `NL_PM`
    (shape `[4096, 64] = [2*2048, 64]`). Then the SM router output (topk `.snd.fst`
    over the full logits) equals `allGather0` of the two PM shard routers (topk
    `.snd.fst` over each dim-0 chunk of `NL_PM`).

    This is provable directly from `allGather0_reconstruct_chunks_2d` (chunk
    reconstruction) composed with the imported topk 2-shard commute
    `fw_topk_routing_snd_fst_allGather0_commute_2_of`. It is graph-independent,
    hence reusable at every layer `k`; the only per-layer work left is the three
    denote unfolds (SM router tid, PM r0/r1 router tids) plus the `NL_SM = NL_PM`
    equality — see the roadmap on `sm_pm_router_commute_layer`. -/
theorem router_commute_of_nl_eq (NL_SM NL_PM : Tensor)
    (hNL : NL_PM.shape = [2 * 2048, 64]) (heq : NL_SM = NL_PM) :
    (fw_topk_routing NL_SM 8 64).snd.fst =
      allGatherPrimDimN 0 2 0
        [(fw_topk_routing (chunkPrimDimN 0 2 0 NL_PM) 8 64).snd.fst,
         (fw_topk_routing (chunkPrimDimN 0 2 1 NL_PM) 8 64).snd.fst] := by
  subst heq
  have hc : ∀ r, (chunkPrimDimN 0 2 r NL_SM).shape = [2048, 64] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r NL_SM [2 * 2048, 64] hNL (by omega)]
    simp only [List.set, List.getD_cons_zero]
  have hrecon := allGather0_reconstruct_chunks_2d 2048 64 (by omega) (by omega) NL_SM hNL
  conv_lhs => rw [← hrecon]
  rw [TrainVerify.Denote.GeneratedPatterns.fw_topk_routing_snd_fst_allGather0_commute_2_of
        (chunkPrimDimN 0 2 0 NL_SM) (chunkPrimDimN 0 2 1 NL_SM)
        2048 8 64 (by omega) (by omega) (hc 0) (hc 1)]

/-! ### L0 denote-unfold template (kernel-clean, validated reduction infra).

    Concrete worked example of the per-layer "reduction infra": reduce a router
    output tid in the ring-attn fold down to the closed `fw_topk_routing …` form.
    Proved for layer 0 (SM tid 4710; PM r0 tid 7483; PM r1 tid 7484) via
    `foldl_prefix_eq_full_ringAttn` (jump full graph → dependency-cone prefix),
    `applyNodeRingAttn_eq_applyNode_of_not_ring` (topk is not a ring op), and
    `applyNode_fw_topk_routing_map_out` (`.snd.fst` = second output). The identical
    schema replicates at every layer by substituting the layer's router/logits
    tids and node indices (read off `sm_goal_3_faithful` / `pm_goal_3_faithful`).

    Together with `router_commute_of_nl_eq`, ChunkPrim unfolds (`7479 =
    chunk0 4708`, `7480 = chunk1 4708`) and the logits shape, the *only* remaining
    obligation for layer 0's router commute is `denote SM 4708 = denote PM 4708`
    (the carry-derived norm-linear equality of step 2/3 in the roadmap below). -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_faithful_4710 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4710 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3_faithful initSM 4708) 8
        (((denoteGraph_ringAttn sm_goal_3_faithful initSM 4708).shape.reverse.head?).getD 1)).snd.fst := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4710 =
      (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4710 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4710 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4710 27 (by decide) (by decide)
  rw [hEntry]
  rw [show sm_goal_3_faithful.nodes.take 27 = sm_goal_3_faithful.nodes.take 26 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [4708], outs := [4709, 4710, 4711], params := [8] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 26).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_topk_routing", ins := [4708], outs := [4709, 4710, 4711], params := [8] } (by decide) (by decide)]
  rw [applyNode_fw_topk_routing_map_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 26).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4708 4709 4710 4711 [8] (by decide)]
  have hval_4708 : (((sm_goal_3_faithful.nodes.take 26).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4708 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4708 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4708 26 (by decide) (by decide)).symm
  rw [hval_4708]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_7483 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7483 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3_faithful initPM 7479) 8
        (((denoteGraph_ringAttn pm_goal_3_faithful initPM 7479).shape.reverse.head?).getD 1)).snd.fst := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7483 =
      (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7483 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7483 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7483 92 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 92 = pm_goal_3_faithful.nodes.take 91 ++ [{ rank := 0, op := "OpName.FW_topk_routing", ins := [7479], outs := [7481, 7483, 7485], params := [8] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 91).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_topk_routing", ins := [7479], outs := [7481, 7483, 7485], params := [8] } (by decide) (by decide)]
  rw [applyNode_fw_topk_routing_map_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 91).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7479 7481 7483 7485 [8] (by decide)]
  have hval : (((pm_goal_3_faithful.nodes.take 91).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7479 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7479 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7479 91 (by decide) (by decide)).symm
  rw [hval]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_7484 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7484 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3_faithful initPM 7480) 8
        (((denoteGraph_ringAttn pm_goal_3_faithful initPM 7480).shape.reverse.head?).getD 1)).snd.fst := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7484 =
      (((pm_goal_3_faithful.nodes.take 93).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7484 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7484 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7484 93 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 93 = pm_goal_3_faithful.nodes.take 92 ++ [{ rank := 1, op := "OpName.FW_topk_routing", ins := [7480], outs := [7482, 7484, 7486], params := [8] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_topk_routing", ins := [7480], outs := [7482, 7484, 7486], params := [8] } (by decide) (by decide)]
  rw [applyNode_fw_topk_routing_map_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7480 7482 7484 7486 [8] (by decide)]
  have hval : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7480 = denoteGraph_ringAttn pm_goal_3_faithful initPM 7480 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7480 92 (by decide) (by decide)).symm
  rw [hval]
  rfl

/-! ### L0 attention-input denote-unfold infra (kernel-clean, Worker F).

    The SM layer-0 attention subgraph (`sm_goal_3_faithful.nodes.take 9`, tids
    4680–4696) is **byte-identical** to the legacy `sm_goal_3` prefix, so these
    Q/K/V denote-unfolds transfer verbatim under the graph rename (verified). They
    reduce the ring-attn fold at the rotary-applied query/key (4692/4693) and the
    value projection (4689) to closed `fw_rotary_embedding` / `fw_per_head_linear`
    forms — the pre-attention half of `sm_pm_carry_L0` (roadmap step 3). The two
    graph-independent helpers below (`storeSet_zip_replicate_mem`,
    `applyNode_fw_multiref_out`) back the `FW_multiref` reductions in these chains
    and every downstream layer's unfolds. -/

theorem storeSet_zip_replicate_mem (s : Store) (v : Tensor) :
    ∀ (outs : List Tid) (t : Tid), t ∈ outs →
      storeSet s (outs.zip (List.replicate outs.length v)) t = v := by
  intro outs
  induction outs with
  | nil => intro t h; nomatch h
  | cons a as ih =>
    intro t h
    by_cases hat : a = t
    · subst hat
      simp [storeSet, List.replicate, List.zip]
    · have hmem : t ∈ as := by
        rcases List.mem_cons.mp h with h1 | h2
        · exact absurd h1.symm hat
        · exact h2
      have hne : ¬ (a = t) := hat
      simp only [List.length_cons, List.replicate, List.zip_cons_cons, storeSet,
        List.find?, hne]
      exact ih t hmem

theorem applyNode_fw_multiref_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t : Tid) (outs : List Tid) (n : Nat)
    (hn : outs.length = n) (hmem : t ∈ outs) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := outs, params := [n] } t = s xTid := by
  unfold applyNode
  subst hn
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  exact storeSet_zip_replicate_mem s (s xTid) outs t hmem

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_faithful_4692 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4692 =
      ((fw_rotary_embedding (initSM 4691) (initSM 4690) (fw_per_head_linear (fw_rms_norm (initSM 4680) (initSM 4682)) (initSM 4684)) (fw_per_head_linear (fw_rms_norm (initSM 4680) (initSM 4682)) (initSM 4686)) 16 4).1) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4692 =
      (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4692 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4692 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4692 8 (by decide) (by decide)
  rw [hEntry]
  rw [show sm_goal_3_faithful.nodes.take 8 = sm_goal_3_faithful.nodes.take 7 ++ [{ rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] } (by decide) (by decide)]
  rw [applyNode_fw_rotary_embedding_fst_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 16 4 4691 4690 4685 4687 4692 4693]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4685 7 8 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4687 7 8 (by omega) (by decide) (by decide)]
  simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 7) initSM 4691 (by decide) (by decide),
      foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 7) initSM 4690 (by decide) (by decide)]
  have hval_4687 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4687 = (fw_per_head_linear ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7396) (initSM 4686)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4687 6 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 6 = sm_goal_3_faithful.nodes.take 5 ++ [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7396, 4686], outs := [4687] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 5).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7396, 4686], outs := [4687] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 5).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7396 4686 4687 []]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7396 5 8 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 5) initSM 4686 (by decide) (by decide)]
  have hval_4685 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4685 = (fw_per_head_linear ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7392) (initSM 4684)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4685 5 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 5 = sm_goal_3_faithful.nodes.take 4 ++ [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7392, 4684], outs := [4685] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 4).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7392, 4684], outs := [4685] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 4).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7392 4684 4685 []]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7392 4 8 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 4) initSM 4684 (by decide) (by decide)]
  have hval_7392 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7392 = ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7392 4 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 4 = sm_goal_3_faithful.nodes.take 3 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4683 7392 [7392, 7396, 7400] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4683 3 8 (by omega) (by decide) (by decide)]
  have hval_7396 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7396 = ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7396 4 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 4 = sm_goal_3_faithful.nodes.take 3 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4683 7396 [7392, 7396, 7400] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4683 3 8 (by omega) (by decide) (by decide)]
  have hval_4683 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4683 = (fw_rms_norm ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7383) (initSM 4682)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4683 3 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 3 = sm_goal_3_faithful.nodes.take 2 ++ [{ rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 2).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 2).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7383 4682 4683]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7383 2 8 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 2) initSM 4682 (by decide) (by decide)]
  have hval_7383 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7383 = ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7383 2 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 2 = sm_goal_3_faithful.nodes.take 1 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4681 7383 [7383, 7387] 2 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4681 1 8 (by omega) (by decide) (by decide)]
  have hval_4681 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4681 = (initSM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4681 1 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 1 = sm_goal_3_faithful.nodes.take 0 ++ [{ rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 0) initSM 4680 (by decide) (by decide)]
  rw [hval_4687, hval_4685, hval_7392, hval_7396, hval_4683, hval_7383, hval_4681]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_faithful_4693 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4693 =
      ((fw_rotary_embedding (initSM 4691) (initSM 4690) (fw_per_head_linear (fw_rms_norm (initSM 4680) (initSM 4682)) (initSM 4684)) (fw_per_head_linear (fw_rms_norm (initSM 4680) (initSM 4682)) (initSM 4686)) 16 4).2) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4693 =
      (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4693 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4693 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4693 8 (by decide) (by decide)
  rw [hEntry]
  rw [show sm_goal_3_faithful.nodes.take 8 = sm_goal_3_faithful.nodes.take 7 ++ [{ rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] } (by decide) (by decide)]
  rw [applyNode_fw_rotary_embedding_snd_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 16 4 4691 4690 4685 4687 4692 4693 (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4685 7 8 (by omega) (by decide) (by decide)]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4687 7 8 (by omega) (by decide) (by decide)]
  simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 7) initSM 4691 (by decide) (by decide),
      foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 7) initSM 4690 (by decide) (by decide)]
  have hval_4687 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4687 = (fw_per_head_linear ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7396) (initSM 4686)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4687 6 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 6 = sm_goal_3_faithful.nodes.take 5 ++ [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7396, 4686], outs := [4687] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 5).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7396, 4686], outs := [4687] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 5).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7396 4686 4687 []]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7396 5 8 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 5) initSM 4686 (by decide) (by decide)]
  have hval_4685 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4685 = (fw_per_head_linear ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7392) (initSM 4684)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4685 5 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 5 = sm_goal_3_faithful.nodes.take 4 ++ [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7392, 4684], outs := [4685] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 4).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7392, 4684], outs := [4685] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 4).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7392 4684 4685 []]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7392 4 8 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 4) initSM 4684 (by decide) (by decide)]
  have hval_7392 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7392 = ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7392 4 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 4 = sm_goal_3_faithful.nodes.take 3 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4683 7392 [7392, 7396, 7400] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4683 3 8 (by omega) (by decide) (by decide)]
  have hval_7396 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7396 = ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7396 4 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 4 = sm_goal_3_faithful.nodes.take 3 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4683 7396 [7392, 7396, 7400] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4683 3 8 (by omega) (by decide) (by decide)]
  have hval_4683 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4683 = (fw_rms_norm ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7383) (initSM 4682)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4683 3 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 3 = sm_goal_3_faithful.nodes.take 2 ++ [{ rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 2).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 2).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7383 4682 4683]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7383 2 8 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 2) initSM 4682 (by decide) (by decide)]
  have hval_7383 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7383 = ((((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7383 2 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 2 = sm_goal_3_faithful.nodes.take 1 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4681 7383 [7383, 7387] 2 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4681 1 8 (by omega) (by decide) (by decide)]
  have hval_4681 : (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4681 = (initSM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4681 1 8 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 1 = sm_goal_3_faithful.nodes.take 0 ++ [{ rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 0) initSM 4680 (by decide) (by decide)]
  rw [hval_4687, hval_4685, hval_7392, hval_7396, hval_4683, hval_7383, hval_4681]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_faithful_4689 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4689 =
      (fw_per_head_linear (fw_rms_norm (initSM 4680) (initSM 4682)) (initSM 4688)) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4689 =
      (((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4689 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4689 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4689 7 (by decide) (by decide)
  rw [hEntry]
  rw [show sm_goal_3_faithful.nodes.take 7 = sm_goal_3_faithful.nodes.take 6 ++ [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7400, 4688], outs := [4689] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 6).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7400, 4688], outs := [4689] } (by decide) (by decide)]
  rw [applyNode_fw_per_head_mix_precision_linear_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 6).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7400 4688 4689 []]
  rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7400 6 7 (by omega) (by decide) (by decide)]
  simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 6) initSM 4688 (by decide) (by decide)]
  have hval_7400 : (((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7400 = ((((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7400 4 7 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 4 = sm_goal_3_faithful.nodes.take 3 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 3).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4683 7400 [7392, 7396, 7400] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4683 3 7 (by omega) (by decide) (by decide)]
  have hval_4683 : (((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4683 = (fw_rms_norm ((((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7383) (initSM 4682)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4683 3 7 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 3 = sm_goal_3_faithful.nodes.take 2 ++ [{ rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 2).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 2).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7383 4682 4683]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7383 2 7 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 2) initSM 4682 (by decide) (by decide)]
  have hval_7383 : (((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7383 = ((((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7383 2 7 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 2 = sm_goal_3_faithful.nodes.take 1 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4681 7383 [7383, 7387] 2 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4681 1 7 (by omega) (by decide) (by decide)]
  have hval_4681 : (((sm_goal_3_faithful.nodes.take 7).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4681 = (initSM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4681 1 7 (by omega) (by decide) (by decide),
      show sm_goal_3_faithful.nodes.take 1 = sm_goal_3_faithful.nodes.take 0 ++ [{ rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 0) initSM 4680 (by decide) (by decide)]
  rw [hval_7400, hval_4683, hval_7383, hval_4681]
  try rfl




-- ============================================================
-- Worker G: L0 end-to-end router commute (kernel-clean spike)
-- ============================================================
-- Block helpers: valAt_fw_view, valAt_allGather0_3d_g, carry_view_commute

theorem valAt_fw_view (sh : Shape) (t : Tensor) (k : Nat)
    (hp : prodShape sh = prodShape t.shape) :
    valAt (fw_view sh t) k = valAt t k := by
  unfold fw_view valAt
  simp only [Tensor.mkShape]
  by_cases hk : k < prodShape sh
  · rw [dif_pos hk, dif_pos (hp ▸ hk)]
  · rw [dif_neg hk, dif_neg (hp ▸ hk)]

theorem valAt_allGather0_3d_g (E h d : Nat) (hE : 0 < E) (hh : 0 < h) (hd : 0 < d)
    (Ws : List Tensor)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [E, h, d])
    (r : Nat) (hr : r < 2) (eLocal : Nat) (heLocal : eLocal < E)
    (hi : Nat) (hi_lt : hi < h) (di : Nat) (hdi_lt : di < d) :
    valAt (allGatherPrimDimN 0 2 0 Ws) (((r * E + eLocal) * h + hi) * d + di)
      = valAt (Ws.getD r (zeroTensor [E, h, d])) ((eLocal * h + hi) * d + di) := by
  unfold allGatherPrimDimN
  rw [hhead]
  simp only [List.drop, List.foldl, List.getD]
  -- shape after set = [E * 2, h, d]
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
    show ((r * E + eLocal) * h + hi) * d + di < prodShape ([E, h, d].set 0 (([E, h, d].getD 0 0) * 2))
    simp [prodShape, List.set, List.getD, List.foldl]
    linarith [hout_bound])]
  simp [Tensor.mkShape, List.set, List.getD, List.drop, List.foldl]
  -- The mkShape function computes valAt (Ws.getD r' _) (preIdx * dimStride + jLocal * postStride + k)
  -- shardShape=[E,h,d], gatherDim=0.
  -- dimSize = E, fullDimSize = E*2, postStride = h*d, dimStride = E*h*d, fullDimStride = E*2*h*d
  set idx := ((r * E + eLocal) * h + hi) * d + di with hidx_def
  have hE_ne : E ≠ 0 := Nat.pos_iff_ne_zero.mp hE
  have hh_ne : h ≠ 0 := Nat.pos_iff_ne_zero.mp hh
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have hE2_ne : E * 2 ≠ 0 := Nat.mul_ne_zero hE_ne (by omega)
  have hhd_ne : h * d ≠ 0 := Nat.mul_ne_zero hh_ne hd_ne
  have hEhd_ne : E * 2 * (h * d) ≠ 0 := Nat.mul_ne_zero hE2_ne hhd_ne
  -- Show: idx / (E*2*(h*d)) = 0 (since idx < E*2*h*d)
  have hidx_bound2 : idx < E * 2 * (h * d) := by
    rw [hidx_def]; simp only [Nat.mul_assoc]; convert hout_bound using 1; ring
  have hpre_div : idx / (E * 2 * (h * d)) = 0 := Nat.div_eq_of_lt hidx_bound2
  have hpre_mod : idx % (E * 2 * (h * d)) = idx := Nat.mod_eq_of_lt hidx_bound2
  -- jFull = idx / (h*d)
  have hjFull_val : idx / (h * d) = r * E + eLocal := by
    rw [hidx_def]
    have h1 : ((r * E + eLocal) * h + hi) * d + di
        = ((r * E + eLocal) * h + hi) * d + di := rfl
    have h2 : ((r * E + eLocal) * h + hi) * d + di = (r * E + eLocal) * (h * d) + (hi * d + di) := by
      ring
    rw [h2]
    have h_small_lt : hi * d + di < h * d := by
      calc hi * d + di < hi * d + d := by omega
        _ = (hi + 1) * d := by ring
        _ ≤ h * d := Nat.mul_le_mul_right _ (by omega)
    have h_div : ((r * E + eLocal) * (h * d) + (hi * d + di)) / (h * d)
        = (hi * d + di) / (h * d) + (r * E + eLocal) := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity)]
    rw [h_div, Nat.div_eq_of_lt h_small_lt]; ring
  -- k = idx % (h*d)
  have hk_val : idx % (h * d) = hi * d + di := by
    rw [hidx_def]
    have h2 : ((r * E + eLocal) * h + hi) * d + di = (r * E + eLocal) * (h * d) + (hi * d + di) := by
      ring
    rw [h2]
    have h_small_lt : hi * d + di < h * d := by
      calc hi * d + di < hi * d + d := by omega
        _ = (hi + 1) * d := by ring
        _ ≤ h * d := Nat.mul_le_mul_right _ (by omega)
    have h_mod : ((r * E + eLocal) * (h * d) + (hi * d + di)) % (h * d)
        = (hi * d + di) % (h * d) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h_mod, Nat.mod_eq_of_lt h_small_lt]
  -- r' = jFull / E = r (since eLocal < E)
  have hr'_val : (r * E + eLocal) / E = r := by
    have h1 : (r * E + eLocal) / E = eLocal / E + r := by
      rw [Nat.add_comm, Nat.add_mul_div_right eLocal r hE]
    rw [h1, Nat.div_eq_of_lt heLocal]; ring
  -- jLocal = jFull % E = eLocal
  have hjLocal_val : (r * E + eLocal) % E = eLocal := by
    have h1 : (r * E + eLocal) % E = eLocal % E := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h1, Nat.mod_eq_of_lt heLocal]
  -- Also idx % (E * 2 * (h * d)) / (h * d) = idx / (h * d) since idx < E*2*(h*d)
  -- And idx % (E * 2 * (h * d)) % (h * d) = idx % (h * d) similarly
  simp [hE_ne, hh_ne, hd_ne, hE2_ne, hhd_ne, hEhd_ne, hpre_div, hpre_mod, hjFull_val, hk_val,
        hr'_val, hjLocal_val]
  -- Remaining: valAt (Ws.getD r _) (0 * (E * (h * d)) + eLocal * (h * d) + (hi * d + di))
  --        =? valAt (Ws.getD r _) ((eLocal * h + hi) * d + di)
  ring_nf

theorem carry_view_commute (a b : Tensor)
    (ha : a.shape = [2048, 16, 64]) (hb : b.shape = [2048, 16, 64]) :
    fw_view [4096, 1024] (fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [a, b]))
      = allGatherPrimDimN 0 2 0
          [fw_view [2048, 1024] (fw_view [2048, 1024] a),
           fw_view [2048, 1024] (fw_view [2048, 1024] b)] := by
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] a)).shape = [2048, 1024] := by
    simp [fw_view, Tensor.mkShape]
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] b)).shape = [2048, 1024] := by
    simp [fw_view, Tensor.mkShape]
  have hAB_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [4096, 16, 64] := by
    have := allGatherPrimDimN_shape 0 2 [a, b] [2048, 16, 64] (by simp [ha])
    simpa using this
  have hRHS_shape : (allGatherPrimDimN 0 2 0
      [fw_view [2048, 1024] (fw_view [2048, 1024] a),
       fw_view [2048, 1024] (fw_view [2048, 1024] b)]).shape = [4096, 1024] := by
    have := allGatherPrimDimN_shape 0 2
      [fw_view [2048, 1024] (fw_view [2048, 1024] a),
       fw_view [2048, 1024] (fw_view [2048, 1024] b)] [2048, 1024] (by simp [hva])
    simpa using this
  apply Tensor.ext
  · rw [hRHS_shape]; simp [fw_view, Tensor.mkShape]
  · intro k hk
    have hkbound : k < 4194304 := by
      simp [fw_view, Tensor.mkShape, prodShape] at hk; omega
    -- LHS valAt = valAt (allGather [a,b]) k
    rw [valAt_fw_view [4096,1024] (fw_view [4096,1024] (allGatherPrimDimN 0 2 0 [a,b])) k
          (by simp [fw_view, Tensor.mkShape, prodShape])]
    rw [valAt_fw_view [4096,1024] (allGatherPrimDimN 0 2 0 [a,b]) k
          (by rw [hAB_shape]; simp [prodShape])]
    -- decompose k
    set r := k / 2097152 with hr_def
    set rem := k % 2097152 with hrem_def
    set eLocal := rem / 1024 with heL_def
    set m := rem % 1024 with hm_def
    set hi := m / 64 with hhi_def
    set di := m % 64 with hdi_def
    have hr2 : r < 2 := by rw [hr_def]; omega
    have hrem_lt : rem < 2097152 := by rw [hrem_def]; omega
    have heL_lt : eLocal < 2048 := by rw [heL_def]; omega
    have hm_lt : m < 1024 := by rw [hm_def]; omega
    have hhi_lt : hi < 16 := by rw [hhi_def]; omega
    have hdi_lt : di < 64 := by rw [hdi_def]; omega
    have hrem_split : rem = eLocal * 1024 + m := by
      rw [heL_def, hm_def]; omega
    have hm_split : m = hi * 64 + di := by rw [hhi_def, hdi_def]; omega
    have hk_split : k = r * 2097152 + rem := by rw [hr_def, hrem_def]; omega
    have hkform1 : k = ((r * 2048 + eLocal) * 16 + hi) * 64 + di := by
      rw [hk_split, hrem_split, hm_split]; ring
    have hkform2 : k = (r * 2048 + eLocal) * 1024 + (hi * 64 + di) := by
      rw [hk_split, hrem_split, hm_split]; ring
    -- RHS via 2D lemma
    rw [show k = (r * 2048 + eLocal) * 1024 + (hi * 64 + di) from hkform2]
    rw [allGatherPrimDimN0_valAt 2 2048 1024
        [fw_view [2048,1024] (fw_view [2048,1024] a),
         fw_view [2048,1024] (fw_view [2048,1024] b)]
        (by norm_num) (by norm_num) (by norm_num)
        (by simp [hva]) (by intro rr hrr; interval_cases rr <;> simp [hva, hvb])
        r hr2 eLocal heL_lt (hi * 64 + di) (by omega)]
    -- LHS via 3d lemma
    rw [show ((r * 2048 + eLocal) * 1024 + (hi * 64 + di)) = ((r * 2048 + eLocal) * 16 + hi) * 64 + di from by ring]
    rw [valAt_allGather0_3d_g 2048 16 64 (by norm_num) (by norm_num) (by norm_num)
        [a, b] (by simp [ha]) r hr2 eLocal heL_lt hi hhi_lt di hdi_lt]
    -- now reduce both getD via interval_cases and valAt_fw_view
    interval_cases r <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] <;>
      rw [valAt_fw_view [2048,1024] _ _ (by simp [fw_view, Tensor.mkShape, ha, hb, prodShape]),
          valAt_fw_view [2048,1024] _ _ (by simp [fw_view, Tensor.mkShape, ha, hb, prodShape])] <;>
      ring_nf


-- Blocks A-D: 3d reconstruction, shapes, PM qkv unfolds, attention commute

-- ===== BLOCK A: graph-independent 3d reconstruction =====
private theorem gather0_3d_valAt
    (numParts Lshard d1 d2 : Nat)
    (Ws : List Tensor)
    (hparts : 0 < numParts) (hL : 0 < Lshard) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [Lshard, d1, d2])
    (r : Nat) (hr : r < numParts)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1)
    (inner : Nat) (hinner : inner < d2) :
    valAt (allGatherPrimDimN 0 numParts 0 Ws)
          (((r * Lshard + row) * d1 + col) * d2 + inner) =
      valAt (Ws.getD r (zeroTensor [Lshard, d1, d2]))
            ((row * d1 + col) * d2 + inner) := by
  have hP_pos : 0 < d1 * d2 := Nat.mul_pos hd1 hd2
  have hP_ne : d1 * d2 ≠ 0 := Nat.ne_of_gt hP_pos
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hE_pos : 0 < Lshard * numParts * (d1 * d2) :=
    Nat.mul_pos (Nat.mul_pos hL hparts) hP_pos
  have hE_ne : Lshard * numParts * (d1 * d2) ≠ 0 := Nat.ne_of_gt hE_pos
  have hlow : col * d2 + inner < d1 * d2 := by
    calc col * d2 + inner < col * d2 + d2 := by omega
      _ = (col + 1) * d2 := by ring
      _ ≤ d1 * d2 := Nat.mul_le_mul_right _ (by omega)
  have hrr : r * Lshard + row < Lshard * numParts := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ numParts * Lshard := Nat.mul_le_mul_right _ hr
    calc r * Lshard + row < (r + 1) * Lshard := hsi
      _ ≤ numParts * Lshard := hle
      _ = Lshard * numParts := by ring
  have hidx_eq : ((r * Lshard + row) * d1 + col) * d2 + inner
      = (col * d2 + inner) + (d1 * d2) * (r * Lshard + row) := by ring
  have hidx_lt_E : ((r * Lshard + row) * d1 + col) * d2 + inner
      < Lshard * numParts * (d1 * d2) := by
    rw [hidx_eq]
    calc (col * d2 + inner) + (d1 * d2) * (r * Lshard + row)
        < (d1 * d2) + (d1 * d2) * (r * Lshard + row) := by omega
      _ = (d1 * d2) * (r * Lshard + row + 1) := by ring
      _ ≤ (d1 * d2) * (Lshard * numParts) := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * numParts * (d1 * d2) := by ring
  have hdiv_E : (((r * Lshard + row) * d1 + col) * d2 + inner)
      / (Lshard * numParts * (d1 * d2)) = 0 := Nat.div_eq_of_lt hidx_lt_E
  have hmod_E : (((r * Lshard + row) * d1 + col) * d2 + inner)
      % (Lshard * numParts * (d1 * d2))
      = ((r * Lshard + row) * d1 + col) * d2 + inner := Nat.mod_eq_of_lt hidx_lt_E
  have hdiv_P : (((r * Lshard + row) * d1 + col) * d2 + inner) / (d1 * d2)
      = r * Lshard + row := by
    rw [hidx_eq, Nat.add_mul_div_left _ _ hP_pos, Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hmod_P : (((r * Lshard + row) * d1 + col) * d2 + inner) % (d1 * d2)
      = col * d2 + inner := by
    rw [hidx_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hdiv_L : (r * Lshard + row) / Lshard = r := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hrow, Nat.zero_add]
  have hmod_L : (r * Lshard + row) % Lshard = row := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have hshape_out : (allGatherPrimDimN 0 numParts 0 Ws).shape
      = [Lshard * numParts, d1, d2] := by
    have := allGatherPrimDimN_shape 0 numParts Ws [Lshard, d1, d2] hhead
    simpa using this
  have hidx_lt_prod : ((r * Lshard + row) * d1 + col) * d2 + inner
      < prodShape (allGatherPrimDimN 0 numParts 0 Ws).shape := by
    rw [hshape_out]
    have hpe : prodShape [Lshard * numParts, d1, d2] = Lshard * numParts * (d1 * d2) := by
      simp [prodShape]; ring
    rw [hpe]; exact hidx_lt_E
  have h0 : valAt (allGatherPrimDimN 0 numParts 0 Ws)
        (((r * Lshard + row) * d1 + col) * d2 + inner)
      = (allGatherPrimDimN 0 numParts 0 Ws).val
          ⟨((r * Lshard + row) * d1 + col) * d2 + inner, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    hP_ne, hL_ne, hE_ne, ite_false]
  rw [hmod_E, hdiv_E, hdiv_P, hmod_P, hdiv_L, hmod_L]
  rw [show 0 * (Lshard * (d1 * d2)) + row * (d1 * d2) + (col * d2 + inner)
        = (row * d1 + col) * d2 + inner from by ring]

/-- Chunk value-at (dim 0, numParts 2): reading local index `(row,col,inner)` of the
    r-th chunk of `T : [2*Lshard, d1, d2]` reads `T` at the full index. -/
private theorem chunk0_3d_valAt
    (Lshard d1 d2 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1, d2])
    (r : Nat) (hr : r < 2)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1)
    (inner : Nat) (hinner : inner < d2) :
    valAt (chunkPrimDimN 0 2 r T) ((row * d1 + col) * d2 + inner) =
      valAt T (((r * Lshard + row) * d1 + col) * d2 + inner) := by
  have hP_pos : 0 < d1 * d2 := Nat.mul_pos hd1 hd2
  have hP_ne : d1 * d2 ≠ 0 := Nat.ne_of_gt hP_pos
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hLd_pos : 0 < Lshard * (d1 * d2) := Nat.mul_pos hL hP_pos
  have hLd_ne : Lshard * (d1 * d2) ≠ 0 := Nat.ne_of_gt hLd_pos
  have hlow : col * d2 + inner < d1 * d2 := by
    calc col * d2 + inner < col * d2 + d2 := by omega
      _ = (col + 1) * d2 := by ring
      _ ≤ d1 * d2 := Nat.mul_le_mul_right _ (by omega)
  -- local index in canonical form
  have hloc_eq : (row * d1 + col) * d2 + inner
      = (col * d2 + inner) + (d1 * d2) * row := by ring
  have hloc_lt : (row * d1 + col) * d2 + inner < Lshard * (d1 * d2) := by
    rw [hloc_eq]
    calc (col * d2 + inner) + (d1 * d2) * row
        < (d1 * d2) + (d1 * d2) * row := by omega
      _ = (d1 * d2) * (row + 1) := by ring
      _ ≤ (d1 * d2) * Lshard := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * (d1 * d2) := by ring
  have hdiv_S : ((row * d1 + col) * d2 + inner) / (Lshard * (d1 * d2)) = 0 :=
    Nat.div_eq_of_lt hloc_lt
  have hmod_S : ((row * d1 + col) * d2 + inner) % (Lshard * (d1 * d2))
      = (row * d1 + col) * d2 + inner := Nat.mod_eq_of_lt hloc_lt
  have hdiv_P : ((row * d1 + col) * d2 + inner) / (d1 * d2) = row := by
    rw [hloc_eq, Nat.add_mul_div_left _ _ hP_pos, Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hmod_P : ((row * d1 + col) * d2 + inner) % (d1 * d2) = col * d2 + inner := by
    rw [hloc_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hrmod : r % 2 = r := Nat.mod_eq_of_lt hr
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  -- chunk shape
  have hchunk_shape : (chunkPrimDimN 0 2 r T).shape = [Lshard, d1, d2] := by
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1, d2] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [hsh]
  have hloc_lt_prod : (row * d1 + col) * d2 + inner
      < prodShape (chunkPrimDimN 0 2 r T).shape := by
    rw [hchunk_shape]
    have hpe : prodShape [Lshard, d1, d2] = Lshard * (d1 * d2) := by simp [prodShape]; ring
    rw [hpe]; exact hloc_lt
  -- T index bound
  have hfull_eq : ((r * Lshard + row) * d1 + col) * d2 + inner
      = (col * d2 + inner) + (d1 * d2) * (r * Lshard + row) := by ring
  have hrr : r * Lshard + row < 2 * Lshard := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ 2 * Lshard := Nat.mul_le_mul_right _ (by omega)
    exact lt_of_lt_of_le hsi hle
  have hfull_lt : ((r * Lshard + row) * d1 + col) * d2 + inner < prodShape T.shape := by
    rw [hT]
    have hpe : prodShape [2 * Lshard, d1, d2] = 2 * Lshard * (d1 * d2) := by
      simp [prodShape]; ring
    rw [hpe, hfull_eq]
    calc (col * d2 + inner) + (d1 * d2) * (r * Lshard + row)
        < (d1 * d2) + (d1 * d2) * (r * Lshard + row) := by omega
      _ = (d1 * d2) * (r * Lshard + row + 1) := by ring
      _ ≤ (d1 * d2) * (2 * Lshard) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Lshard * (d1 * d2) := by ring
  rw [valAt_of_lt _ _ hloc_lt_prod]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hT, List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    show ((2:Nat) = 0) = False from by decide, ite_false,
    hsh, hrmod, hP_ne, hLd_ne]
  rw [hmod_S, hdiv_S, hdiv_P, hmod_P]
  congr 1
  ring

/-- Ring-attention reconstruction (numParts = 2, seq dim = 0):
    gathering the two seq-chunks of a `[2*Lshard, d1, d2]` tensor rebuilds it. -/
theorem allGather0_reconstruct_chunks_3d
    (Lshard d1 d2 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1, d2]) :
    allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T] = T := by
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  have hc_shape : ∀ r, (chunkPrimDimN 0 2 r T).shape = [Lshard, d1, d2] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1, d2] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]; rw [hsh]
  have hhead : (([chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].head?.map
      (fun t => t.shape)).getD []) = [Lshard, d1, d2] := by simp [hc_shape 0]
  have hgshape : (allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T]).shape
      = [2 * Lshard, d1, d2] := by
    rw [allGatherPrimDimN_shape 0 2 _ [Lshard, d1, d2] hhead]
    simp only [List.set, List.getD_cons_zero]; rw [Nat.mul_comm Lshard 2]
  apply Tensor.ext
  · rw [hgshape, hT]
  · intro idx hidx
    rw [hgshape] at hidx
    have hprod : prodShape [2 * Lshard, d1, d2] = 2 * Lshard * (d1 * d2) := by
      simp [prodShape]; ring
    rw [hprod] at hidx
    set inner := idx % d2 with hinner_def
    set col := (idx / d2) % d1 with hcol_def
    set fullrow := (idx / d2 / d1) with hfullrow_def
    have hinner : inner < d2 := by rw [hinner_def]; exact Nat.mod_lt _ hd2
    have hcol : col < d1 := by rw [hcol_def]; exact Nat.mod_lt _ hd1
    have hfullrow_lt : fullrow < 2 * Lshard := by
      rw [hfullrow_def]
      apply Nat.div_lt_of_lt_mul
      apply Nat.div_lt_of_lt_mul
      calc idx < 2 * Lshard * (d1 * d2) := hidx
        _ = d2 * (d1 * (2 * Lshard)) := by ring
    set r := fullrow / Lshard with hr_def
    set row := fullrow % Lshard with hrow_def
    have hrow : row < Lshard := by rw [hrow_def]; exact Nat.mod_lt _ hL
    have hr : r < 2 := by
      rw [hr_def]
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact hfullrow_lt
    have hfullrow_split : fullrow = r * Lshard + row := by
      rw [hr_def, hrow_def]; rw [Nat.mul_comm]; exact (Nat.div_add_mod fullrow Lshard).symm
    have hidx_decomp : idx = ((r * Lshard + row) * d1 + col) * d2 + inner := by
      rw [← hfullrow_split]
      rw [hinner_def, hcol_def, hfullrow_def]
      -- idx = ((idx/d2/d1)*d1 + (idx/d2)%d1)*d2 + idx%d2
      have e1 : (idx / d2 / d1) * d1 + (idx / d2) % d1 = idx / d2 := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod (idx / d2) d1
      rw [e1]
      rw [Nat.mul_comm (idx / d2) d2]
      exact (Nat.div_add_mod idx d2).symm
    rw [hidx_decomp]
    rw [gather0_3d_valAt 2 Lshard d1 d2 _ (by omega) hL hd1 hd2 hhead r hr row hrow col hcol inner hinner]
    have hgetD : [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].getD r (zeroTensor [Lshard, d1, d2])
        = chunkPrimDimN 0 2 r T := by
      interval_cases r <;> rfl
    rw [hgetD]
    exact chunk0_3d_valAt Lshard d1 d2 hL hd1 hd2 T hT r hr row hrow col hcol inner hinner

/-- PM-side buddy-pair unfold for `applyNodeRingAttn_sliding_window` (mirror of
    the zigzag version — identical reconstruction shape). -/
theorem applyNodeRingAttn_sliding_window_pair_eq_chunk
    (g : GraphDecl) (s : Store) (n n0 n1 : NodeDecl)
    (idx : Nat)
    (hbuddy : ringAttnBuddies g n = [n0, n1])
    (hmyIdx : (([n0, n1].findIdx? (fun m => m.rank = n.rank)).getD 0) = idx) :
    applyNodeRingAttn_sliding_window g s n =
      chunkPrimDimN 0 2 idx
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 0 0), s (n1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 1 0), s (n1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 2 0), s (n1.ins.getD 2 0)])
          (s (n.ins.getD 3 0)) (s (n.ins.getD 4 0))
          (n.params.getD 0 1) (n.params.getD 1 1) (n.params.getD 2 1) (n.params.getD 3 1)
          (decide (n.params.getD 4 0 ≠ 0)) (n.params.getD 5 0)) := by
  unfold applyNodeRingAttn_sliding_window
  rw [hbuddy]
  simp only [List.map, List.length_cons, List.length_nil, hmyIdx]

theorem applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    (g_sm g_pm : GraphDecl) (s_sm s_pm : Store)
    (n_sm n_pm_r0 n_pm_r1 : NodeDecl)
    (Lshard qh vd : Nat)
    (hL : 0 < Lshard) (hqh : 0 < qh) (hvd : 0 < vd)
    (hbuddy_sm : ringAttnBuddies g_sm n_sm = [n_sm])
    (hbuddy_pm : ringAttnBuddies g_pm n_pm_r0 = [n_pm_r0, n_pm_r1])
    (hbuddy_pm' : ringAttnBuddies g_pm n_pm_r1 = [n_pm_r0, n_pm_r1])
    (hmyIdx0 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r0.rank)).getD 0) = 0)
    (hmyIdx1 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r1.rank)).getD 0) = 1)
    (hq_sm : 0 < (s_sm (n_sm.ins.getD 0 0)).shape.length)
    (hk_sm : 0 < (s_sm (n_sm.ins.getD 1 0)).shape.length)
    (hv_sm : 0 < (s_sm (n_sm.ins.getD 2 0)).shape.length)
    (hq_full : s_sm (n_sm.ins.getD 0 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
    (hk_full : s_sm (n_sm.ins.getD 1 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
    (hv_full : s_sm (n_sm.ins.getD 2 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
    (hcuQ_sm_pm : s_sm (n_sm.ins.getD 3 0) = s_pm (n_pm_r0.ins.getD 3 0))
    (hcuK_sm_pm : s_sm (n_sm.ins.getD 4 0) = s_pm (n_pm_r0.ins.getD 4 0))
    (hcuQ_same : s_pm (n_pm_r0.ins.getD 3 0) = s_pm (n_pm_r1.ins.getD 3 0))
    (hcuK_same : s_pm (n_pm_r0.ins.getD 4 0) = s_pm (n_pm_r1.ins.getD 4 0))
    (hparams_sm : n_sm.params = n_pm_r0.params)
    (hparams_same : n_pm_r0.params = n_pm_r1.params)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
          (s_pm (n_pm_r0.ins.getD 3 0)) (s_pm (n_pm_r0.ins.getD 4 0))
          (n_pm_r0.params.getD 0 1) (n_pm_r0.params.getD 1 1) (n_pm_r0.params.getD 2 1)
          (n_pm_r0.params.getD 3 1)
          (decide (n_pm_r0.params.getD 4 0 ≠ 0)) (n_pm_r0.params.getD 5 0)).shape
        = [2 * Lshard, qh, vd]) :
    applyNodeRingAttn_sliding_window g_sm s_sm n_sm =
      allGatherPrimDimN 0 2 0
        [applyNodeRingAttn_sliding_window g_pm s_pm n_pm_r0,
         applyNodeRingAttn_sliding_window g_pm s_pm n_pm_r1] := by
  have hout_sm : 0 < (fw_attn_varlen (s_sm (n_sm.ins.getD 0 0)) (s_sm (n_sm.ins.getD 1 0))
      (s_sm (n_sm.ins.getD 2 0)) (s_sm (n_sm.ins.getD 3 0)) (s_sm (n_sm.ins.getD 4 0))
      (n_sm.params.getD 0 1) (n_sm.params.getD 1 1) (n_sm.params.getD 2 1) (n_sm.params.getD 3 1)
      (decide (n_sm.params.getD 4 0 ≠ 0)) (n_sm.params.getD 5 0)).shape.length := by
    rw [hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm, hfull_shape]
    simp
  rw [applyNodeRingAttn_sliding_window_singleton g_sm s_sm n_sm hbuddy_sm hq_sm hk_sm hv_sm hout_sm,
      hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm]
  rw [applyNodeRingAttn_sliding_window_pair_eq_chunk g_pm s_pm n_pm_r0 n_pm_r0 n_pm_r1 0
        hbuddy_pm hmyIdx0,
      applyNodeRingAttn_sliding_window_pair_eq_chunk g_pm s_pm n_pm_r1 n_pm_r0 n_pm_r1 1
        hbuddy_pm' hmyIdx1]
  rw [← hcuQ_same, ← hcuK_same, ← hparams_same]
  rw [allGather0_reconstruct_chunks_3d Lshard qh vd hL hqh hvd _ hfull_shape]


-- ===== BLOCK B: shape + attn helpers =====
theorem topk_snd_fst_chunk_commute (L : Tensor) (S n k : Nat)
    (hS : 0 < S) (hk : 0 < k) (hL : L.shape = [2 * S, k]) :
    (fw_topk_routing L n k).snd.fst =
      allGatherPrimDimN 0 2 0
        [(fw_topk_routing (chunkPrimDimN 0 2 0 L) n k).snd.fst,
         (fw_topk_routing (chunkPrimDimN 0 2 1 L) n k).snd.fst] := by
  have hchunk := allGather0_reconstruct_chunks_2d S k hS hk L hL
  have hsh : (2 * S) / 2 = S := by omega
  have hc0 : (chunkPrimDimN 0 2 0 L).shape = [S, k] := by
    rw [chunkPrimDimN_shape 0 2 0 L [2 * S, k] hL (by omega)]
    simp only [List.set, List.getD_cons_zero]; rw [hsh]
  have hc1 : (chunkPrimDimN 0 2 1 L).shape = [S, k] := by
    rw [chunkPrimDimN_shape 0 2 1 L [2 * S, k] hL (by omega)]
    simp only [List.set, List.getD_cons_zero]; rw [hsh]
  conv_lhs => rw [← hchunk]
  rw [TrainVerify.Denote.GeneratedPatterns.fw_topk_routing_snd_fst_allGather0_commute_2_of
        (chunkPrimDimN 0 2 0 L) (chunkPrimDimN 0 2 1 L) S n k hS hk hc0 hc1]
theorem rms_sh (x w : Tensor) : (fw_rms_norm x w).shape = x.shape := by
  unfold fw_rms_norm
  cases hrev : x.shape.reverse with
  | nil => simp
  | cons d tl => simp [Tensor.mkShape]

theorem sigmoid_sh (x : Tensor) : (fw_sigmoid x).shape = x.shape := by
  unfold fw_sigmoid; simp [Tensor.mkShape]

theorem view_sh (sh : Shape) (x : Tensor) : (fw_view sh x).shape = sh := by
  unfold fw_view; simp [Tensor.mkShape]

theorem ewadd_eq (x y : Tensor) (s : Shape) (hx : x.shape = s) (hy : y.shape = s) :
    (elemwiseAdd x y).shape = s :=
  elemwiseAdd_shape_of_shapes x y s hx hy
theorem chunk0_2 (r : Nat) (x : Tensor) (a b : Nat) (h : x.shape = [a, b]) :
    (chunkPrimDimN 0 2 r x).shape = [a / 2, b] := by
  rw [chunkPrimDimN_shape 0 2 r x [a, b] h (by omega)]
  simp [List.set]

theorem nl_sh (b k n : Nat) (x w : Tensor)
    (hx : x.shape = [b, k]) (hw : w.shape = [n, k]) :
    (fw_norm_linear x w).shape = [b, n] := by
  unfold fw_norm_linear; rw [hx, hw]; simp [Tensor.mkShape]

theorem topk_sf_sh (x : Tensor) (S topK numExp : Nat) (hx : x.shape = [S, numExp]) :
    (fw_topk_routing x topK numExp).snd.fst.shape = [S, numExp] := by
  unfold fw_topk_routing; simp [Tensor.mkShape]; rw [hx]; rfl
theorem attn_sw_store_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hcuQ : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hcuK : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_sliding_window g s n = applyNodeRingAttn_sliding_window g s' n := by
  unfold applyNodeRingAttn_sliding_window
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hcuQ, hcuK]

-- shape helpers parametric in store
theorem ph_shape_p3 (st : Store) (wtid : Tid) (nh : Nat)
    (h80 : (st 4680).shape = [4096, 1024]) (h82 : (st 4682).shape = [1024])
    (hw : (st wtid).shape = [nh, 64, 1024]) :
    (fw_per_head_linear (fw_rms_norm (st 4680) (st 4682)) (st wtid)).shape = [4096, nh, 64] := by
  unfold fw_per_head_linear
  rw [(rms_sh (st 4680) (st 4682)).trans h80, hw]; simp [Tensor.mkShape]

theorem qrot_shape_p3 (st : Store)
    (h80 : (st 4680).shape = [4096, 1024]) (h82 : (st 4682).shape = [1024])
    (h84 : (st 4684).shape = [16, 64, 1024]) (h86 : (st 4686).shape = [4, 64, 1024]) :
    ((fw_rotary_embedding (st 4691) (st 4690)
        (fw_per_head_linear (fw_rms_norm (st 4680) (st 4682)) (st 4684))
        (fw_per_head_linear (fw_rms_norm (st 4680) (st 4682)) (st 4686)) 16 4).1).shape
      = [4096, 16, 64] := by
  show (fw_rotary_apply (st 4691) (st 4690) _ 16).shape = [4096, 16, 64]
  exact fw_rotary_apply_shape_c2a _ _ _ 4096 16 64 (ph_shape_p3 st 4684 16 h80 h82 h84)

theorem krot_shape_p3 (st : Store)
    (h80 : (st 4680).shape = [4096, 1024]) (h82 : (st 4682).shape = [1024])
    (h84 : (st 4684).shape = [16, 64, 1024]) (h86 : (st 4686).shape = [4, 64, 1024]) :
    ((fw_rotary_embedding (st 4691) (st 4690)
        (fw_per_head_linear (fw_rms_norm (st 4680) (st 4682)) (st 4684))
        (fw_per_head_linear (fw_rms_norm (st 4680) (st 4682)) (st 4686)) 16 4).2).shape
      = [4096, 4, 64] := by
  show (fw_rotary_apply (st 4691) (st 4690) _ 4).shape = [4096, 4, 64]
  exact fw_rotary_apply_shape_c2a _ _ _ 4096 4 64 (ph_shape_p3 st 4686 4 h80 h82 h86)

theorem fw_attn_varlen_shape_p3 (q k v cuQ cuK : Tensor) (qh kvh d vd wl : Nat) (causal : Bool) :
    (fw_attn_varlen q k v cuQ cuK qh kvh d vd causal wl).shape = [(q.shape.head?).getD 0, qh, vd] := by
  unfold fw_attn_varlen; simp [Tensor.mkShape]


-- ===== BLOCK C: PM qkv unfolds + qkv commutes =====
theorem denote_pm_goal_3_qproj_0_r0 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7433 =
      (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0 ((fw_rotary_embedding (initPM 4691) (initPM 4690) (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4684)) (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4686)) 16 4).1)) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7433 =
      (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7433 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7433 41 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 41 = pm_goal_3_faithful.nodes.take 40 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [4692], outs := [7433], params := [0] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.ChunkPrim", ins := [4692], outs := [7433], params := [0] } (by decide) (by decide)]
  rw [applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 4692 7433 0]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4692 40 41 (by omega) (by decide) (by decide)]
  have hval_4692 : (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4692 = ((fw_rotary_embedding ((((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11853) (initPM 4690) ((((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4685) ((((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4687) 16 4).1) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4692 38 41 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 38 = pm_goal_3_faithful.nodes.take 37 ++ [{ rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 37).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] } (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 37).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 16 4 11853 4690 4685 4687 4692 4693]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11853 37 41 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4685 37 41 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4687 37 41 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 37) initPM 4690 (by decide) (by decide)]
  have hval_4687 : (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4687 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14636) (initPM 4686)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4687 35 41 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 35 = pm_goal_3_faithful.nodes.take 34 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 34).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 34).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14636 4686 4687 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14636 34 41 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 34) initPM 4686 (by decide) (by decide)]
  have hval_4685 : (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4685 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14632) (initPM 4684)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4685 34 41 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 34 = pm_goal_3_faithful.nodes.take 33 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 33).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 33).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14632 4684 4685 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14632 33 41 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 33) initPM 4684 (by decide) (by decide)]
  have hval_14632 : (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14632 = ((((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14632 30 41 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14632 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 41 (by omega) (by decide) (by decide)]
  have hval_14636 : (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14636 = ((((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14636 30 41 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14636 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 41 (by omega) (by decide) (by decide)]
  have hval_4683 : (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683 = (fw_rms_norm ((((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611) (initPM 4682)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 28 41 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 28 = pm_goal_3_faithful.nodes.take 27 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14611 4682 4683]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 27 41 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 27) initPM 4682 (by decide) (by decide)]
  have hval_14611 : (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611 = ((((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 26 41 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 26 = pm_goal_3_faithful.nodes.take 25 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4681 14611 [14611, 14615] 2 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 25 41 (by omega) (by decide) (by decide)]
  have hval_4681 : (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681 = (initPM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 24 41 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 24 = pm_goal_3_faithful.nodes.take 23 ++ [{ rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 23) initPM 4680 (by decide) (by decide)]
  have hval_11853 : (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11853 = (initPM 4691) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11853 12 41 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 12 = pm_goal_3_faithful.nodes.take 11 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864], params := [12] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864], params := [12] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4691 11853 [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864] 12 rfl (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 11) initPM 4691 (by decide) (by decide)]
  rw [hval_4692, hval_4687, hval_4685, hval_14632, hval_14636, hval_4683, hval_14611, hval_4681, hval_11853]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_kproj_0_r0 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7435 =
      (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0 ((fw_rotary_embedding (initPM 4691) (initPM 4690) (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4684)) (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4686)) 16 4).2)) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7435 =
      (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7435 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7435 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7435 42 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 42 = pm_goal_3_faithful.nodes.take 41 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [4693], outs := [7435], params := [0] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.ChunkPrim", ins := [4693], outs := [7435], params := [0] } (by decide) (by decide)]
  rw [applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 41).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 4693 7435 0]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4693 41 42 (by omega) (by decide) (by decide)]
  have hval_4693 : (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4693 = ((fw_rotary_embedding ((((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11853) (initPM 4690) ((((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4685) ((((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4687) 16 4).2) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4693 38 42 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 38 = pm_goal_3_faithful.nodes.take 37 ++ [{ rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 37).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] } (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 37).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 16 4 11853 4690 4685 4687 4692 4693 (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11853 37 42 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4685 37 42 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4687 37 42 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 37) initPM 4690 (by decide) (by decide)]
  have hval_4687 : (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4687 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14636) (initPM 4686)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4687 35 42 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 35 = pm_goal_3_faithful.nodes.take 34 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 34).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 34).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14636 4686 4687 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14636 34 42 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 34) initPM 4686 (by decide) (by decide)]
  have hval_4685 : (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4685 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14632) (initPM 4684)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4685 34 42 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 34 = pm_goal_3_faithful.nodes.take 33 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 33).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 33).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14632 4684 4685 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14632 33 42 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 33) initPM 4684 (by decide) (by decide)]
  have hval_14632 : (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14632 = ((((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14632 30 42 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14632 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 42 (by omega) (by decide) (by decide)]
  have hval_14636 : (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14636 = ((((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14636 30 42 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14636 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 42 (by omega) (by decide) (by decide)]
  have hval_4683 : (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683 = (fw_rms_norm ((((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611) (initPM 4682)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 28 42 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 28 = pm_goal_3_faithful.nodes.take 27 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14611 4682 4683]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 27 42 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 27) initPM 4682 (by decide) (by decide)]
  have hval_14611 : (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611 = ((((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 26 42 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 26 = pm_goal_3_faithful.nodes.take 25 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4681 14611 [14611, 14615] 2 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 25 42 (by omega) (by decide) (by decide)]
  have hval_4681 : (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681 = (initPM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 24 42 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 24 = pm_goal_3_faithful.nodes.take 23 ++ [{ rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 23) initPM 4680 (by decide) (by decide)]
  have hval_11853 : (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11853 = (initPM 4691) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11853 12 42 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 12 = pm_goal_3_faithful.nodes.take 11 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864], params := [12] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864], params := [12] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4691 11853 [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864] 12 rfl (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 11) initPM 4691 (by decide) (by decide)]
  rw [hval_4693, hval_4687, hval_4685, hval_14632, hval_14636, hval_4683, hval_14611, hval_4681, hval_11853]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_vproj_0_r0 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7421 =
      (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 0 (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4688))) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7421 =
      (((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7421 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7421 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7421 39 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 39 = pm_goal_3_faithful.nodes.take 38 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [4689], outs := [7421], params := [0] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 38).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.ChunkPrim", ins := [4689], outs := [7421], params := [0] } (by decide) (by decide)]
  rw [applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 38).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 4689 7421 0]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4689 38 39 (by omega) (by decide) (by decide)]
  have hval_4689 : (((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4689 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14640) (initPM 4688)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4689 36 39 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 36 = pm_goal_3_faithful.nodes.take 35 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14640, 4688], outs := [4689] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 35).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14640, 4688], outs := [4689] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 35).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14640 4688 4689 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14640 35 39 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 35) initPM 4688 (by decide) (by decide)]
  have hval_14640 : (((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14640 = ((((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14640 30 39 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14640 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 39 (by omega) (by decide) (by decide)]
  have hval_4683 : (((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683 = (fw_rms_norm ((((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611) (initPM 4682)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 28 39 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 28 = pm_goal_3_faithful.nodes.take 27 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14611 4682 4683]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 27 39 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 27) initPM 4682 (by decide) (by decide)]
  have hval_14611 : (((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611 = ((((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 26 39 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 26 = pm_goal_3_faithful.nodes.take 25 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4681 14611 [14611, 14615] 2 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 25 39 (by omega) (by decide) (by decide)]
  have hval_4681 : (((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681 = (initPM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 24 39 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 24 = pm_goal_3_faithful.nodes.take 23 ++ [{ rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 23) initPM 4680 (by decide) (by decide)]
  rw [hval_4689, hval_14640, hval_4683, hval_14611, hval_4681]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_qproj_0_r1 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7434 =
      (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1 ((fw_rotary_embedding (initPM 4691) (initPM 4690) (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4684)) (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4686)) 16 4).1)) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7434 =
      (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7434 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7434 43 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 43 = pm_goal_3_faithful.nodes.take 42 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [4692], outs := [7434], params := [0] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.ChunkPrim", ins := [4692], outs := [7434], params := [0] } (by decide) (by decide)]
  rw [applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 42).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4692 7434 0]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4692 42 43 (by omega) (by decide) (by decide)]
  have hval_4692 : (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4692 = ((fw_rotary_embedding ((((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11853) (initPM 4690) ((((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4685) ((((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4687) 16 4).1) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4692 38 43 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 38 = pm_goal_3_faithful.nodes.take 37 ++ [{ rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 37).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] } (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 37).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 16 4 11853 4690 4685 4687 4692 4693]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11853 37 43 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4685 37 43 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4687 37 43 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 37) initPM 4690 (by decide) (by decide)]
  have hval_4687 : (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4687 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14636) (initPM 4686)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4687 35 43 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 35 = pm_goal_3_faithful.nodes.take 34 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 34).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 34).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14636 4686 4687 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14636 34 43 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 34) initPM 4686 (by decide) (by decide)]
  have hval_4685 : (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4685 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14632) (initPM 4684)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4685 34 43 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 34 = pm_goal_3_faithful.nodes.take 33 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 33).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 33).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14632 4684 4685 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14632 33 43 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 33) initPM 4684 (by decide) (by decide)]
  have hval_14632 : (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14632 = ((((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14632 30 43 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14632 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 43 (by omega) (by decide) (by decide)]
  have hval_14636 : (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14636 = ((((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14636 30 43 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14636 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 43 (by omega) (by decide) (by decide)]
  have hval_4683 : (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683 = (fw_rms_norm ((((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611) (initPM 4682)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 28 43 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 28 = pm_goal_3_faithful.nodes.take 27 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14611 4682 4683]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 27 43 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 27) initPM 4682 (by decide) (by decide)]
  have hval_14611 : (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611 = ((((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 26 43 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 26 = pm_goal_3_faithful.nodes.take 25 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4681 14611 [14611, 14615] 2 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 25 43 (by omega) (by decide) (by decide)]
  have hval_4681 : (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681 = (initPM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 24 43 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 24 = pm_goal_3_faithful.nodes.take 23 ++ [{ rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 23) initPM 4680 (by decide) (by decide)]
  have hval_11853 : (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11853 = (initPM 4691) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11853 12 43 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 12 = pm_goal_3_faithful.nodes.take 11 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864], params := [12] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864], params := [12] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4691 11853 [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864] 12 rfl (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 11) initPM 4691 (by decide) (by decide)]
  rw [hval_4692, hval_4687, hval_4685, hval_14632, hval_14636, hval_4683, hval_14611, hval_4681, hval_11853]
  try rfl

-- Phase 5b.5.2 (multiref-init-fix follow-through): the L0 Q-projection
-- reconstruction commutes — the SM full q-proj tensor equals the all-gather
-- (over dim 0, the token dim) of the two PM rank shards.
--
-- This is the base case that the second upstream fidelity fix
-- (`initGoal_4691.tps -> source leaf 4691`) unblocks: the rotary cos/sin
-- table boundary equality `initSM 4691 = initPM 4691` is now extractable from
-- `InitGoalsHold goal_3_cut_initGoals`, which was previously underivable when
-- `initGoal_4691.tps` pointed at the multiref copy 11853.  All the weight
-- boundary equalities (4680 via goal_5, 4682/4684/4686/4690/4691 via the
-- identity init goals) come straight from `InitGoalsHold`; the reconstruction
-- itself is `allGather0_reconstruct_chunks_3d`.  Kernel-only axioms.
set_option maxHeartbeats 1600000 in
theorem sm_pm_qproj_L0_commute
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM)
    (hT : ((fw_rotary_embedding (initPM 4691) (initPM 4690)
              (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4684))
              (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4686)) 16 4).1).shape
            = [2 * 2048, 4, 64]) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4692
      = allGatherPrimDimN 0 2 0
          [ denoteGraph_ringAttn pm_goal_3_faithful initPM 7433,
            denoteGraph_ringAttn pm_goal_3_faithful initPM 7434 ] := by
  have hII : InitGoalsHold pm_goal_3_faithful.numRanks initGoals initSM initPM := by
    intro g hg
    exact hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb : ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
    intro g hg hshape
    have hgh := hII g hg
    unfold InitGoalHolds at hgh
    obtain ⟨_, _, hval⟩ := hgh
    rw [hshape] at hval
    simpa [List.map, reconstructWithDim_singleton] using hval
  have h4682 : initSM 4682 = initPM 4682 := hb initGoal_4682 (by decide) rfl
  have h4684 : initSM 4684 = initPM 4684 := hb initGoal_4684 (by decide) rfl
  have h4686 : initSM 4686 = initPM 4686 := hb initGoal_4686 (by decide) rfl
  have h4690 : initSM 4690 = initPM 4690 := hb initGoal_4690 (by decide) rfl
  have h4691 : initSM 4691 = initPM 4691 := hb initGoal_4691 (by decide) rfl
  have h4680 : initSM 4680 = initPM 4680 := by
    have hg := hInit goal_5
      (by unfold goal_3_cut_initGoals goal_3_prereqs; exact List.mem_append_right _ (by simp))
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simpa [goal_5, List.map, reconstructWithDim_singleton] using hval
  rw [denote_sm_goal_3_faithful_4692, denote_pm_goal_3_qproj_0_r0, denote_pm_goal_3_qproj_0_r1]
  rw [h4680, h4682, h4684, h4686, h4690, h4691]
  rw [show pm_goal_3_faithful.numRanks = 2 from rfl]
  exact (allGather0_reconstruct_chunks_3d 2048 4 64 (by omega) (by omega) (by omega) _ hT).symm

set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_kproj_0_r1 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7436 =
      (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1 ((fw_rotary_embedding (initPM 4691) (initPM 4690) (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4684)) (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4686)) 16 4).2)) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7436 =
      (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7436 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7436 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7436 44 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 44 = pm_goal_3_faithful.nodes.take 43 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [4693], outs := [7436], params := [0] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.ChunkPrim", ins := [4693], outs := [7436], params := [0] } (by decide) (by decide)]
  rw [applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 43).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4693 7436 0]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4693 43 44 (by omega) (by decide) (by decide)]
  have hval_4693 : (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4693 = ((fw_rotary_embedding ((((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11853) (initPM 4690) ((((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4685) ((((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4687) 16 4).2) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4693 38 44 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 38 = pm_goal_3_faithful.nodes.take 37 ++ [{ rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 37).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] } (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 37).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 16 4 11853 4690 4685 4687 4692 4693 (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11853 37 44 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4685 37 44 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4687 37 44 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 37) initPM 4690 (by decide) (by decide)]
  have hval_4687 : (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4687 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14636) (initPM 4686)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4687 35 44 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 35 = pm_goal_3_faithful.nodes.take 34 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 34).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 34).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14636 4686 4687 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14636 34 44 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 34) initPM 4686 (by decide) (by decide)]
  have hval_4685 : (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4685 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14632) (initPM 4684)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4685 34 44 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 34 = pm_goal_3_faithful.nodes.take 33 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 33).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 33).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14632 4684 4685 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14632 33 44 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 33) initPM 4684 (by decide) (by decide)]
  have hval_14632 : (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14632 = ((((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14632 30 44 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14632 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 44 (by omega) (by decide) (by decide)]
  have hval_14636 : (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14636 = ((((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14636 30 44 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14636 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 44 (by omega) (by decide) (by decide)]
  have hval_4683 : (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683 = (fw_rms_norm ((((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611) (initPM 4682)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 28 44 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 28 = pm_goal_3_faithful.nodes.take 27 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14611 4682 4683]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 27 44 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 27) initPM 4682 (by decide) (by decide)]
  have hval_14611 : (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611 = ((((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 26 44 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 26 = pm_goal_3_faithful.nodes.take 25 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4681 14611 [14611, 14615] 2 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 25 44 (by omega) (by decide) (by decide)]
  have hval_4681 : (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681 = (initPM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 24 44 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 24 = pm_goal_3_faithful.nodes.take 23 ++ [{ rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 23) initPM 4680 (by decide) (by decide)]
  have hval_11853 : (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 11853 = (initPM 4691) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11853 12 44 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 12 = pm_goal_3_faithful.nodes.take 11 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864], params := [12] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864], params := [12] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4691 11853 [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864] 12 rfl (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 11) initPM 4691 (by decide) (by decide)]
  rw [hval_4693, hval_4687, hval_4685, hval_14632, hval_14636, hval_4683, hval_14611, hval_4681, hval_11853]
  try rfl

set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_vproj_0_r1 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7422 =
      (chunkPrimDimN 0 pm_goal_3_faithful.numRanks 1 (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4688))) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7422 =
      (((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7422 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7422 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7422 40 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 40 = pm_goal_3_faithful.nodes.take 39 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [4689], outs := [7422], params := [0] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.ChunkPrim", ins := [4689], outs := [7422], params := [0] } (by decide) (by decide)]
  rw [applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 39).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4689 7422 0]
  rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4689 39 40 (by omega) (by decide) (by decide)]
  have hval_4689 : (((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4689 = (fw_per_head_linear ((((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14640) (initPM 4688)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4689 36 40 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 36 = pm_goal_3_faithful.nodes.take 35 ++ [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14640, 4688], outs := [4689] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 35).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14640, 4688], outs := [4689] } (by decide) (by decide),
      applyNode_fw_per_head_mix_precision_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 35).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14640 4688 4689 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14640 35 40 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 35) initPM 4688 (by decide) (by decide)]
  have hval_14640 : (((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14640 = ((((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14640 30 40 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 30 = pm_goal_3_faithful.nodes.take 29 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 29).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4683 14640 [14632, 14636, 14640] 3 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 29 40 (by omega) (by decide) (by decide)]
  have hval_4683 : (((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4683 = (fw_rms_norm ((((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611) (initPM 4682)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4683 28 40 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 28 = pm_goal_3_faithful.nodes.take 27 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14611 4682 4683]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 27 40 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 27) initPM 4682 (by decide) (by decide)]
  have hval_14611 : (((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14611 = ((((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14611 26 40 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 26 = pm_goal_3_faithful.nodes.take 25 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4681 14611 [14611, 14615] 2 rfl (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 25 40 (by omega) (by decide) (by decide)]
  have hval_4681 : (((pm_goal_3_faithful.nodes.take 40).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681 = (initPM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 24 40 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 24 = pm_goal_3_faithful.nodes.take 23 ++ [{ rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 23) initPM 4680 (by decide) (by decide)]
  rw [hval_4689, hval_14640, hval_4683, hval_14611, hval_4681]
  try rfl

-- L0 K-projection reconstruction commute: the SM full K-projection output (rotary .2)
-- equals the allGather of the two per-rank PM chunks.  Mirrors `sm_pm_qproj_L0_commute`.
-- Weight boundary equalities extracted from `InitGoalsHold`; closed by
-- `allGather0_reconstruct_chunks_3d`.  Kernel-only axioms.
theorem sm_pm_kproj_L0_commute
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM)
    (hT : ((fw_rotary_embedding (initPM 4691) (initPM 4690)
              (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4684))
              (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4686)) 16 4).2).shape
            = [2 * 2048, 4, 64]) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4693
      = allGatherPrimDimN 0 2 0
          [ denoteGraph_ringAttn pm_goal_3_faithful initPM 7435,
            denoteGraph_ringAttn pm_goal_3_faithful initPM 7436 ] := by
  have hII : InitGoalsHold pm_goal_3_faithful.numRanks initGoals initSM initPM := by
    intro g hg
    exact hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb : ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
    intro g hg hshape
    have hgh := hII g hg
    unfold InitGoalHolds at hgh
    obtain ⟨_, _, hval⟩ := hgh
    rw [hshape] at hval
    simpa [List.map, reconstructWithDim_singleton] using hval
  have h4682 : initSM 4682 = initPM 4682 := hb initGoal_4682 (by decide) rfl
  have h4684 : initSM 4684 = initPM 4684 := hb initGoal_4684 (by decide) rfl
  have h4686 : initSM 4686 = initPM 4686 := hb initGoal_4686 (by decide) rfl
  have h4690 : initSM 4690 = initPM 4690 := hb initGoal_4690 (by decide) rfl
  have h4691 : initSM 4691 = initPM 4691 := hb initGoal_4691 (by decide) rfl
  have h4680 : initSM 4680 = initPM 4680 := by
    have hg := hInit goal_5
      (by unfold goal_3_cut_initGoals goal_3_prereqs; exact List.mem_append_right _ (by simp))
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simpa [goal_5, List.map, reconstructWithDim_singleton] using hval
  rw [denote_sm_goal_3_faithful_4693, denote_pm_goal_3_kproj_0_r0, denote_pm_goal_3_kproj_0_r1]
  rw [h4680, h4682, h4684, h4686, h4690, h4691]
  rw [show pm_goal_3_faithful.numRanks = 2 from rfl]
  exact (allGather0_reconstruct_chunks_3d 2048 4 64 (by omega) (by omega) (by omega) _ hT).symm

-- L0 V-projection reconstruction commute: the SM full V-projection output
-- (`fw_per_head_linear` of the rms-normed hidden, no rotary) equals the allGather of the
-- two per-rank PM chunks.  Mirrors `sm_pm_qproj_L0_commute`; only weights 4680/4682/4688
-- participate.  Kernel-only axioms.
theorem sm_pm_vproj_L0_commute
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM)
    (hT : (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4688)).shape
            = [2 * 2048, 4, 64]) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4689
      = allGatherPrimDimN 0 2 0
          [ denoteGraph_ringAttn pm_goal_3_faithful initPM 7421,
            denoteGraph_ringAttn pm_goal_3_faithful initPM 7422 ] := by
  have hII : InitGoalsHold pm_goal_3_faithful.numRanks initGoals initSM initPM := by
    intro g hg
    exact hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb : ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
    intro g hg hshape
    have hgh := hII g hg
    unfold InitGoalHolds at hgh
    obtain ⟨_, _, hval⟩ := hgh
    rw [hshape] at hval
    simpa [List.map, reconstructWithDim_singleton] using hval
  have h4682 : initSM 4682 = initPM 4682 := hb initGoal_4682 (by decide) rfl
  have h4688 : initSM 4688 = initPM 4688 := hb initGoal_4688 (by decide) rfl
  have h4680 : initSM 4680 = initPM 4680 := by
    have hg := hInit goal_5
      (by unfold goal_3_cut_initGoals goal_3_prereqs; exact List.mem_append_right _ (by simp))
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simpa [goal_5, List.map, reconstructWithDim_singleton] using hval
  rw [denote_sm_goal_3_faithful_4689, denote_pm_goal_3_vproj_0_r0, denote_pm_goal_3_vproj_0_r1]
  rw [h4680, h4682, h4688]
  rw [show pm_goal_3_faithful.numRanks = 2 from rfl]
  exact (allGather0_reconstruct_chunks_3d 2048 4 64 (by omega) (by omega) (by omega) _ hT).symm



-- ===== BLOCK D: node defs + buddy + attention commute =====
def nSM : NodeDecl := { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] }
def nR0 : NodeDecl := { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7433, 7435, 7421, 4694, 4695], outs := [7437], params := [16, 4, 64, 64, 1, 512] }
def nR1 : NodeDecl := { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7434, 7436, 7422, 4694, 4695], outs := [7438], params := [16, 4, 64, 64, 1, 512] }

-- buddy facts (kernel-clean)
theorem buddy_sm : ringAttnBuddies sm_goal_3_faithful nSM = [nSM] := by
  show (List.filter (fun m => decide (m.op = nSM.op) && decide (m.params = nSM.params) &&
      decide (m.ins.getD 3 0 = nSM.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM.ins.getD 4 0))
      sm_goal_3_faithful.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM]
  rw [show (List.filter (fun m => decide (m.op = nSM.op) && decide (m.params = nSM.params) &&
      decide (m.ins.getD 3 0 = nSM.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM.ins.getD 4 0))
      sm_goal_3_faithful.nodes) = [nSM] from by rfl]
  simp

theorem buddy_r0 : ringAttnBuddies pm_goal_3_faithful nR0 = [nR0, nR1] := by
  show (List.filter (fun m => decide (m.op = nR0.op) && decide (m.params = nR0.params) &&
      decide (m.ins.getD 3 0 = nR0.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0.ins.getD 4 0))
      pm_goal_3_faithful.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0, nR1]
  rw [show (List.filter (fun m => decide (m.op = nR0.op) && decide (m.params = nR0.params) &&
      decide (m.ins.getD 3 0 = nR0.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0.ins.getD 4 0))
      pm_goal_3_faithful.nodes) = [nR0, nR1] from by rfl]
  apply List.mergeSort_of_pairwise; decide

theorem buddy_r1 : ringAttnBuddies pm_goal_3_faithful nR1 = [nR0, nR1] := by
  show (List.filter (fun m => decide (m.op = nR1.op) && decide (m.params = nR1.params) &&
      decide (m.ins.getD 3 0 = nR1.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1.ins.getD 4 0))
      pm_goal_3_faithful.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0, nR1]
  rw [show (List.filter (fun m => decide (m.op = nR1.op) && decide (m.params = nR1.params) &&
      decide (m.ins.getD 3 0 = nR1.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1.ins.getD 4 0))
      pm_goal_3_faithful.nodes) = [nR0, nR1] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxHeartbeats 12000000 in
theorem sm_pm_attention_L0_commute
    (initSM initPM : Store)
    (h_ss_sm : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    applyNodeRingAttn_sliding_window sm_goal_3_faithful
        ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)
        { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] }
      = allGatherPrimDimN 0 pm_goal_3_faithful.numRanks 0
          [applyNodeRingAttn_sliding_window pm_goal_3_faithful
             ((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)
             { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7433, 7435, 7421, 4694, 4695], outs := [7437], params := [16, 4, 64, 64, 1, 512] },
           applyNodeRingAttn_sliding_window pm_goal_3_faithful
             ((pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)
             { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7434, 7436, 7422, 4694, 4695], outs := [7438], params := [16, 4, 64, 64, 1, 512] }] := by
  show applyNodeRingAttn_sliding_window sm_goal_3_faithful
        ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM) nSM
      = allGatherPrimDimN 0 2 0
          [applyNodeRingAttn_sliding_window pm_goal_3_faithful
             ((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) nR0,
           applyNodeRingAttn_sliding_window pm_goal_3_faithful
             ((pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) nR1]
  -- weight equalities
  have hII : InitGoalsHold pm_goal_3_faithful.numRanks initGoals initSM initPM := by
    intro g hg
    exact hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb : ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
    intro g hg hshape
    have hgh := hII g hg
    unfold InitGoalHolds at hgh
    obtain ⟨_, _, hval⟩ := hgh
    rw [hshape] at hval
    simpa [List.map, reconstructWithDim_singleton] using hval
  have h4682 : initSM 4682 = initPM 4682 := hb initGoal_4682 (by decide) rfl
  have h4684 : initSM 4684 = initPM 4684 := hb initGoal_4684 (by decide) rfl
  have h4686 : initSM 4686 = initPM 4686 := hb initGoal_4686 (by decide) rfl
  have h4688 : initSM 4688 = initPM 4688 := hb initGoal_4688 (by decide) rfl
  have h4690 : initSM 4690 = initPM 4690 := hb initGoal_4690 (by decide) rfl
  have h4691 : initSM 4691 = initPM 4691 := hb initGoal_4691 (by decide) rfl
  have h4694 : initSM 4694 = initPM 4694 := hb initGoal_4694 (by decide) rfl
  have h4695 : initSM 4695 = initPM 4695 := hb initGoal_4695 (by decide) rfl
  have h4680 : initSM 4680 = initPM 4680 := by
    have hg := hInit goal_5
      (by unfold goal_3_cut_initGoals goal_3_prereqs; exact List.mem_append_right _ (by simp))
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simpa [goal_5, List.map, reconstructWithDim_singleton] using hval
  -- store <-> prefix-fold bridges
  have bSM4692 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4692
      = denoteGraph_ringAttn sm_goal_3_faithful initSM 4692 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4692 8 (by decide) (by decide)).symm
  have bSM4693 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4693
      = denoteGraph_ringAttn sm_goal_3_faithful initSM 4693 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4693 8 (by decide) (by decide)).symm
  have bSM4689 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4689
      = denoteGraph_ringAttn sm_goal_3_faithful initSM 4689 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4689 8 (by decide) (by decide)).symm
  have bPM7433 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7433 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7433 44 (by decide) (by decide)).symm
  have bPM7434 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7434 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7434 44 (by decide) (by decide)).symm
  have bPM7435 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7435
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7435 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7435 44 (by decide) (by decide)).symm
  have bPM7436 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7436
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7436 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7436 44 (by decide) (by decide)).symm
  have bPM7421 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7421
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7421 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7421 44 (by decide) (by decide)).symm
  have bPM7422 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7422
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7422 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7422 44 (by decide) (by decide)).symm
  -- corrected Q reconstruction (16 heads), K and V (4 heads)
  have hT16 : ((fw_rotary_embedding (initPM 4691) (initPM 4690)
        (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4684))
        (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4686)) 16 4).1).shape
      = [2 * 2048, 16, 64] :=
    qrot_shape_p3 initPM (h_ss_pm 4680 [4096,1024] (by decide)) (h_ss_pm 4682 [1024] (by decide))
      (h_ss_pm 4684 [16,64,1024] (by decide)) (h_ss_pm 4686 [4,64,1024] (by decide))
  have qproj16 : denoteGraph_ringAttn sm_goal_3_faithful initSM 4692
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3_faithful initPM 7433, denoteGraph_ringAttn pm_goal_3_faithful initPM 7434] := by
    rw [denote_sm_goal_3_faithful_4692, denote_pm_goal_3_qproj_0_r0, denote_pm_goal_3_qproj_0_r1]
    rw [h4680, h4682, h4684, h4686, h4690, h4691]
    rw [show pm_goal_3_faithful.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega) _ hT16).symm
  have kproj := sm_pm_kproj_L0_commute initSM initPM hInit
    (krot_shape_p3 initPM (h_ss_pm 4680 [4096,1024] (by decide)) (h_ss_pm 4682 [1024] (by decide))
      (h_ss_pm 4684 [16,64,1024] (by decide)) (h_ss_pm 4686 [4,64,1024] (by decide)))
  have vproj := sm_pm_vproj_L0_commute initSM initPM hInit
    (ph_shape_p3 initPM 4688 4 (h_ss_pm 4680 [4096,1024] (by decide)) (h_ss_pm 4682 [1024] (by decide))
      (h_ss_pm 4688 [4,64,1024] (by decide)))
  -- store-level q/k/v full hypotheses
  have hq_full : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4692
      = allGatherPrimDimN 0 2 0
          [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433,
           (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434] := by
    rw [bSM4692, bPM7433, bPM7434]; exact qproj16
  have hk_full : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4693
      = allGatherPrimDimN 0 2 0
          [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7435,
           (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7436] := by
    rw [bSM4693, bPM7435, bPM7436]; exact kproj
  have hv_full : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4689
      = allGatherPrimDimN 0 2 0
          [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7421,
           (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7422] := by
    rw [bSM4689, bPM7421, bPM7422]; exact vproj
  -- shapes of SM inputs
  have hSMq_shape : ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4692).shape
      = [4096, 16, 64] := by
    rw [bSM4692, denote_sm_goal_3_faithful_4692]
    exact qrot_shape_p3 initSM (h_ss_sm 4680 [4096,1024] (by decide)) (h_ss_sm 4682 [1024] (by decide))
      (h_ss_sm 4684 [16,64,1024] (by decide)) (h_ss_sm 4686 [4,64,1024] (by decide))
  have hSMk_shape : ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4693).shape
      = [4096, 4, 64] := by
    rw [bSM4693, denote_sm_goal_3_faithful_4693]
    exact krot_shape_p3 initSM (h_ss_sm 4680 [4096,1024] (by decide)) (h_ss_sm 4682 [1024] (by decide))
      (h_ss_sm 4684 [16,64,1024] (by decide)) (h_ss_sm 4686 [4,64,1024] (by decide))
  have hSMv_shape : ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4689).shape
      = [4096, 4, 64] := by
    rw [bSM4689, denote_sm_goal_3_faithful_4689]
    exact ph_shape_p3 initSM 4688 4 (h_ss_sm 4680 [4096,1024] (by decide)) (h_ss_sm 4682 [1024] (by decide))
      (h_ss_sm 4688 [4,64,1024] (by decide))
  have hq_sm : 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4692).shape.length
    rw [hSMq_shape]; decide
  have hk_sm : 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4693).shape.length
    rw [hSMk_shape]; decide
  have hv_sm : 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4689).shape.length
    rw [hSMv_shape]; decide
  -- cu_seqlens equalities
  have hSM4694 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4694 = initSM 4694 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 8) initSM 4694 (by decide) (by decide)
  have hSM4695 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4695 = initSM 4695 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 8) initSM 4695 (by decide) (by decide)
  have hPM4694 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4694 = initPM 4694 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 44) initPM 4694 (by decide) (by decide)
  have hPM4695 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4695 = initPM 4695 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 44) initPM 4695 (by decide) (by decide)
  have hcuQ_sm_pm : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 3 0)
      = (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 3 0) := by
    show (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4694
        = (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4694
    rw [hSM4694, hPM4694, h4694]
  have hcuK_sm_pm : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 4 0)
      = (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 4 0) := by
    show (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4695
        = (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4695
    rw [hSM4695, hPM4695, h4695]
  -- full attention output shape
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 0 0),
                                  (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 1 0),
                                  (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 2 0),
                                  (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 2 0)])
        ((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 3 0))
        ((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 4 0))
        (nR0.params.getD 0 1) (nR0.params.getD 1 1) (nR0.params.getD 2 1) (nR0.params.getD 3 1)
        (decide (nR0.params.getD 4 0 ≠ 0)) (nR0.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433,
                                    (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, hSMq_shape]; rfl
  -- bridge r1 store take44 -> take45
  have e7433 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7433 44 45 (by omega) (by decide) (by decide)).symm
  have e7434 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7434 44 45 (by omega) (by decide) (by decide)).symm
  have e7435 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7435
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7435 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7435 44 45 (by omega) (by decide) (by decide)).symm
  have e7436 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7436
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7436 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7436 44 45 (by omega) (by decide) (by decide)).symm
  have e7421 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7421
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7421 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7421 44 45 (by omega) (by decide) (by decide)).symm
  have e7422 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7422
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7422 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7422 44 45 (by omega) (by decide) (by decide)).symm
  have e4694b : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4694
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4694 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4694 44 45 (by omega) (by decide) (by decide)).symm
  have e4695b : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4695
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4695 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4695 44 45 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm_goal_3_faithful
        ((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) nR1
      = applyNodeRingAttn_sliding_window pm_goal_3_faithful
        ((pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) nR1 := by
    apply attn_sw_store_congr
    · rw [buddy_r1]; intro m hm; fin_cases hm
      · exact e7433
      · exact e7434
    · rw [buddy_r1]; intro m hm; fin_cases hm
      · exact e7435
      · exact e7436
    · rw [buddy_r1]; intro m hm; fin_cases hm
      · exact e7421
      · exact e7422
    · exact e4694b
    · exact e4695b
  -- apply reconstruction lemma
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm_goal_3_faithful pm_goal_3_faithful
    ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)
    ((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)
    nSM nR0 nR1 2048 16 64 (by omega) (by omega) (by omega)
    buddy_sm buddy_r0 buddy_r1 (by decide) (by decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape
  rw [hrec, bridge_r1]


-- Router-chain denote unfolds (SM/PM 4708, chunks, SM/PM 4703 carry)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_faithful_4708 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4708 =
      fw_norm_linear (fw_rms_norm
        (denoteGraph_ringAttn sm_goal_3_faithful initSM 4703) (initSM 4704)) (initSM 4707) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4708 =
      (((sm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4708 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4708 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4708 23 (by decide) (by decide)
  rw [hEntry]
  -- peel norm_linear (node idx 22)
  rw [show sm_goal_3_faithful.nodes.take 23 = sm_goal_3_faithful.nodes.take 22 ++ [{ rank := 0, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 22).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] } (by decide) (by decide),
      applyNode_fw_norm_linear_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 22).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4706 4707 4708 []]
  -- 4707 is a weight (not written in take 22)
  rw [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 22) initSM 4707 (by decide) (by decide)]
  -- reduce 4706: split at float node idx 18 (take 19)
  rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4706 19 22 (by omega) (by decide) (by decide)]
  rw [show sm_goal_3_faithful.nodes.take 19 = sm_goal_3_faithful.nodes.take 18 ++ [{ rank := 0, op := "OpName.FW_float", ins := [7415], outs := [4706] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 18).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_float", ins := [7415], outs := [4706] } (by decide) (by decide),
      applyNode_fw_float_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 18).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7415 4706 []]
  -- reduce 7415: split at multiref node idx 17 (take 18)
  rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7415 18 18 (by omega) (by decide) (by decide)]
  rw [show sm_goal_3_faithful.nodes.take 18 = sm_goal_3_faithful.nodes.take 17 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 17).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 17).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4705 7415 [7415, 7419, 7423, 7427, 7431] 5 (by decide) (by decide)]
  -- reduce 4705: split at rms_norm node idx 16 (take 17)
  rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4705 17 17 (by omega) (by decide) (by decide)]
  rw [show sm_goal_3_faithful.nodes.take 17 = sm_goal_3_faithful.nodes.take 16 ++ [{ rank := 0, op := "OpName.FW_rms_norm", ins := [7404, 4704], outs := [4705] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 16).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_rms_norm", ins := [7404, 4704], outs := [4705] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 16).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7404 4704 4705]
  -- 4704 is a weight (not written in take 16)
  rw [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 16) initSM 4704 (by decide) (by decide)]
  -- reduce 7404: split at multiref node idx 15 (take 16)
  rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7404 16 16 (by omega) (by decide) (by decide)]
  rw [show sm_goal_3_faithful.nodes.take 16 = sm_goal_3_faithful.nodes.take 15 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 15).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 15).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4703 7404 [7404, 7408] 2 (by decide) (by decide)]
  -- 4703 = denote
  have hval_4703 : (((sm_goal_3_faithful.nodes.take 15).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4703 = denoteGraph_ringAttn sm_goal_3_faithful initSM 4703 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4703 15 (by decide) (by decide)).symm
  rw [hval_4703]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_4708 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 4708 =
      fw_norm_linear (fw_rms_norm
        (denoteGraph_ringAttn pm_goal_3_faithful initPM 4703) (initPM 4704)) (initPM 4707) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 4708 =
      (((pm_goal_3_faithful.nodes.take 77).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4708 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4708 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4708 77 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 77 = pm_goal_3_faithful.nodes.take 76 ++ [{ rank := 1, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 76).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] } (by decide) (by decide),
      applyNode_fw_norm_linear_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 76).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4706 4707 4708 []]
  rw [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 76) initPM 4707 (by decide) (by decide)]
  rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4706 71 76 (by omega) (by decide) (by decide)]
  rw [show pm_goal_3_faithful.nodes.take 71 = pm_goal_3_faithful.nodes.take 70 ++ [{ rank := 1, op := "OpName.FW_float", ins := [11875], outs := [4706] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 70).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_float", ins := [11875], outs := [4706] } (by decide) (by decide),
      applyNode_fw_float_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 70).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 11875 4706 []]
  rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 11875 65 70 (by omega) (by decide) (by decide)]
  rw [show pm_goal_3_faithful.nodes.take 65 = pm_goal_3_faithful.nodes.take 64 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4705], outs := [11875, 11876, 11877, 11878, 11879], params := [5] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 64).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4705], outs := [11875, 11876, 11877, 11878, 11879], params := [5] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 64).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4705 11875 [11875, 11876, 11877, 11878, 11879] 5 (by decide) (by decide)]
  rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4705 63 64 (by omega) (by decide) (by decide)]
  rw [show pm_goal_3_faithful.nodes.take 63 = pm_goal_3_faithful.nodes.take 62 ++ [{ rank := 1, op := "OpName.FW_rms_norm", ins := [14652, 4704], outs := [4705] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 62).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_rms_norm", ins := [14652, 4704], outs := [4705] } (by decide) (by decide),
      applyNode_fw_rms_norm_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 62).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14652 4704 4705]
  rw [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 62) initPM 4704 (by decide) (by decide)]
  rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14652 61 62 (by omega) (by decide) (by decide)]
  rw [show pm_goal_3_faithful.nodes.take 61 = pm_goal_3_faithful.nodes.take 60 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656], params := [2] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 60).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 60).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4703 14652 [14652, 14656] 2 (by decide) (by decide)]
  have hval_4703 : (((pm_goal_3_faithful.nodes.take 60).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4703 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4703 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4703 60 (by decide) (by decide)).symm
  rw [hval_4703]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_7479 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7479 =
      chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm_goal_3_faithful initPM 4708) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7479 =
      (((pm_goal_3_faithful.nodes.take 84).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7479 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7479 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7479 84 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 84 = pm_goal_3_faithful.nodes.take 83 ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [4708], outs := [7479], params := [0] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 83).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.ChunkPrim", ins := [4708], outs := [7479], params := [0] } (by decide) (by decide),
      applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 83).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 4708 7479 0]
  have hval : (((pm_goal_3_faithful.nodes.take 83).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4708 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4708 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4708 83 (by decide) (by decide)).symm
  rw [hval, show pm_goal_3_faithful.numRanks = 2 from rfl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_7480 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 7480 =
      chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm_goal_3_faithful initPM 4708) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 7480 =
      (((pm_goal_3_faithful.nodes.take 85).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7480 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7480 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7480 85 (by decide) (by decide)
  rw [hEntry]
  rw [show pm_goal_3_faithful.nodes.take 85 = pm_goal_3_faithful.nodes.take 84 ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [4708], outs := [7480], params := [0] }] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 84).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.ChunkPrim", ins := [4708], outs := [7480], params := [0] } (by decide) (by decide),
      applyNode_chunkPrimDimN_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 84).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4708 7480 0]
  have hval : (((pm_goal_3_faithful.nodes.take 84).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4708 = denoteGraph_ringAttn pm_goal_3_faithful initPM 4708 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4708 84 (by decide) (by decide)).symm
  rw [hval, show pm_goal_3_faithful.numRanks = 2 from rfl]



set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_faithful_4703 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4703 =
      elemwiseAdd (initSM 4680) (fw_view [4096, 1024] (fw_linear (fw_view [4096, 1024] (fw_view [4096, 1024] (applyNodeRingAttn_sliding_window sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] }))) (initSM 4699))) := by
  have hEntry : denoteGraph_ringAttn sm_goal_3_faithful initSM 4703 =
      (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4703 := by
    show sm_goal_3_faithful.nodes.foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4703 = _
    exact foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4703 27 (by decide) (by decide)
  rw [hEntry]
  have hval_4703 : (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4703 = (elemwiseAdd ((((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7387) ((((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4702)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4703 15 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3_faithful.nodes.take 15 = sm_goal_3_faithful.nodes.take 14 ++ [{ rank := 0, op := "OpName.FW_add", ins := [7387, 4702], outs := [4703] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 14).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_add", ins := [7387, 4702], outs := [4703] } (by decide) (by decide),
      applyNode_fw_add2_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 14).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 7387 4702 4703,
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7387 14 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide),
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4702 14 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4702 : (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4702 = ((((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4701) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4702 14 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3_faithful.nodes.take 14 = sm_goal_3_faithful.nodes.take 13 ++ [{ rank := 0, op := "OpName.FW_float", ins := [4701], outs := [4702] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 13).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_float", ins := [4701], outs := [4702] } (by decide) (by decide),
      applyNode_fw_float_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 13).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4701 4702 [],
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4701 13 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4701 : (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4701 = (fw_view [4096, 1024] ((((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4700)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4701 13 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3_faithful.nodes.take 13 = sm_goal_3_faithful.nodes.take 12 ++ [{ rank := 0, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 12).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] } (by decide) (by decide),
      applyNode_fw_view_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 12).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4096 [1024] 4700 4701,
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4700 12 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4700 : (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4700 = (fw_linear ((((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4698) (initSM 4699)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4700 12 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3_faithful.nodes.take 12 = sm_goal_3_faithful.nodes.take 11 ++ [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] } (by decide) (by decide),
      applyNode_fw_mix_precision_linear_out_1p sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 11).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4698 4699 4700,
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4698 11 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 11) initSM 4699 (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4698 : (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4698 = (fw_view [4096, 1024] ((((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4697)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4698 11 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3_faithful.nodes.take 11 = sm_goal_3_faithful.nodes.take 10 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [4697], outs := [4698], params := [4096, 1024] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 10).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_reshape", ins := [4697], outs := [4698], params := [4096, 1024] } (by decide) (by decide),
      applyNode_fw_reshape_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 10).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4697 4698 [4096, 1024],
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4697 10 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4697 : (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4697 = (fw_view [4096, 1024] ((((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4696)) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4697 10 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3_faithful.nodes.take 10 = sm_goal_3_faithful.nodes.take 9 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [4696], outs := [4697], params := [4096, 1024] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 9).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_reshape", ins := [4696], outs := [4697], params := [4096, 1024] } (by decide) (by decide),
      applyNode_fw_reshape_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 9).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4696 4697 [4096, 1024],
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4696 9 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4696 : (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4696 = applyNodeRingAttn_sliding_window sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] } := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4696 9 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3_faithful.nodes.take 9 = sm_goal_3_faithful.nodes.take 8 ++ [{ rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_sliding_window_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4692 4693 4689 4694 4695 4696 [16, 4, 64, 64, 1, 512]]
  have hval_7387 : (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 7387 = ((((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 7387 2 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3_faithful.nodes.take 2 = sm_goal_3_faithful.nodes.take 1 ++ [{ rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 1).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4681 7387 [7383, 7387] 2 (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4681 1 27 (by omega) (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  have hval_4681 : (((sm_goal_3_faithful.nodes.take 27).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 4681 = (initSM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4681 1 27 (by omega) (by intro n hn; fin_cases hn <;> decide) (by intro n hn; fin_cases hn <;> decide),
      show sm_goal_3_faithful.nodes.take 1 = sm_goal_3_faithful.nodes.take 0 ++ [{ rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out sm_goal_3_faithful (((sm_goal_3_faithful.nodes.take 0).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM)) 0 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 0) initSM 4680 (by intro m hm; fin_cases hm <;> decide) (by intro m hm; fin_cases hm <;> decide)]
  rw [hval_4703, hval_4702, hval_4701, hval_4700, hval_4698, hval_4697, hval_4696, hval_7387, hval_4681]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_faithful_4703 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3_faithful initPM 4703 =
      elemwiseAdd (initPM 4680) (fw_view [4096, 1024] (fw_linear (allGatherPrimDimN 0 pm_goal_3_faithful.numRanks 0 [fw_view [2048, 1024] (fw_view [2048, 1024] (applyNodeRingAttn_sliding_window pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7433, 7435, 7421, 4694, 4695], outs := [7437], params := [16, 4, 64, 64, 1, 512] })), fw_view [2048, 1024] (fw_view [2048, 1024] (applyNodeRingAttn_sliding_window pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7434, 7436, 7422, 4694, 4695], outs := [7438], params := [16, 4, 64, 64, 1, 512] }))]) (initPM 4699))) := by
  have hEntry : denoteGraph_ringAttn pm_goal_3_faithful initPM 4703 =
      (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4703 := by
    show pm_goal_3_faithful.nodes.foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4703 = _
    exact foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4703 92 (by decide) (by decide)
  rw [hEntry]
  have hval_4703 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4703 = (elemwiseAdd ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14615) ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4702)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4703 59 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 59 = pm_goal_3_faithful.nodes.take 58 ++ [{ rank := 1, op := "OpName.FW_add", ins := [14615, 4702], outs := [4703] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_add", ins := [14615, 4702], outs := [4703] } (by decide) (by decide),
      applyNode_fw_add2_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 58).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 14615 4702 4703]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14615 58 92 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4702 58 92 (by omega) (by decide) (by decide)]
  have hval_4702 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4702 = ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4701) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4702 57 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 57 = pm_goal_3_faithful.nodes.take 56 ++ [{ rank := 1, op := "OpName.FW_float", ins := [4701], outs := [4702] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 56).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_float", ins := [4701], outs := [4702] } (by decide) (by decide),
      applyNode_fw_float_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 56).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4701 4702 []]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4701 56 92 (by omega) (by decide) (by decide)]
  have hval_4701 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4701 = (fw_view [4096, 1024] ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4700)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4701 55 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 55 = pm_goal_3_faithful.nodes.take 54 ++ [{ rank := 1, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 54).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] } (by decide) (by decide),
      applyNode_fw_view_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 54).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4096 [1024] 4700 4701]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4700 54 92 (by omega) (by decide) (by decide)]
  have hval_4700 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4700 = (fw_linear ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4698) (initPM 4699)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4700 53 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 53 = pm_goal_3_faithful.nodes.take 52 ++ [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 52).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] } (by decide) (by decide),
      applyNode_fw_mix_precision_linear_out_1p pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 52).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4698 4699 4700]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4698 52 92 (by omega) (by decide) (by decide)]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 52) initPM 4699 (by decide) (by decide)]
  have hval_4698 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4698 = (allGatherPrimDimN 0 pm_goal_3_faithful.numRanks 0 [((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7445), ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7446)]) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4698 51 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 51 = pm_goal_3_faithful.nodes.take 50 ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [7445, 7446], outs := [4698], params := [0] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 50).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.AllGatherPrim", ins := [7445, 7446], outs := [4698], params := [0] } (by decide) (by decide),
      applyNode_allGatherPrimDimN_out_thm pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 50).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 [7445, 7446] 4698 0]
    simp only [List.map_cons, List.map_nil]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7445 50 92 (by omega) (by decide) (by decide),
      ← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7446 50 92 (by omega) (by decide) (by decide)]
  have hval_7446 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7446 = (fw_view [2048, 1024] ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7440)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7446 50 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 50 = pm_goal_3_faithful.nodes.take 49 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [7440], outs := [7446], params := [2048, 1024] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 49).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_reshape", ins := [7440], outs := [7446], params := [2048, 1024] } (by decide) (by decide),
      applyNode_fw_reshape_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 49).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7440 7446 [2048, 1024]]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7440 49 92 (by omega) (by decide) (by decide)]
  have hval_7445 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7445 = (fw_view [2048, 1024] ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7439)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7445 49 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 49 = pm_goal_3_faithful.nodes.take 48 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [7439], outs := [7445], params := [2048, 1024] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 48).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_reshape", ins := [7439], outs := [7445], params := [2048, 1024] } (by decide) (by decide),
      applyNode_fw_reshape_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 48).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7439 7445 [2048, 1024]]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7439 48 92 (by omega) (by decide) (by decide)]
  have hval_7440 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7440 = (fw_view [2048, 1024] ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7438)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7440 48 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 48 = pm_goal_3_faithful.nodes.take 47 ++ [{ rank := 1, op := "OpName.FW_reshape", ins := [7438], outs := [7440], params := [2048, 1024] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 47).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_reshape", ins := [7438], outs := [7440], params := [2048, 1024] } (by decide) (by decide),
      applyNode_fw_reshape_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 47).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7438 7440 [2048, 1024]]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7438 47 92 (by omega) (by decide) (by decide)]
  have hval_7439 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7439 = (fw_view [2048, 1024] ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7437)) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7439 47 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 47 = pm_goal_3_faithful.nodes.take 46 ++ [{ rank := 0, op := "OpName.FW_reshape", ins := [7437], outs := [7439], params := [2048, 1024] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 46).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_reshape", ins := [7437], outs := [7439], params := [2048, 1024] } (by decide) (by decide),
      applyNode_fw_reshape_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 46).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7437 7439 [2048, 1024]]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7437 46 92 (by omega) (by decide) (by decide)]
  have hval_7438 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7438 = applyNodeRingAttn_sliding_window pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7434, 7436, 7422, 4694, 4695], outs := [7438], params := [16, 4, 64, 64, 1, 512] } := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7438 46 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 46 = pm_goal_3_faithful.nodes.take 45 ++ [{ rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7434, 7436, 7422, 4694, 4695], outs := [7438], params := [16, 4, 64, 64, 1, 512] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_sliding_window_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 7434 7436 7422 4694 4695 7438 [16, 4, 64, 64, 1, 512]]
  have hval_7437 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 7437 = applyNodeRingAttn_sliding_window pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7433, 7435, 7421, 4694, 4695], outs := [7437], params := [16, 4, 64, 64, 1, 512] } := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7437 45 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 45 = pm_goal_3_faithful.nodes.take 44 ++ [{ rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7433, 7435, 7421, 4694, 4695], outs := [7437], params := [16, 4, 64, 64, 1, 512] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_sliding_window_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 0 7433 7435 7421 4694 4695 7437 [16, 4, 64, 64, 1, 512]]
  have hval_14615 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 14615 = ((((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 14615 26 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 26 = pm_goal_3_faithful.nodes.take 25 ++ [{ rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] } (by decide) (by decide),
      applyNode_fw_multiref_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 25).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4681 14615 [14611, 14615] 2 (by decide) (by decide)]
    rw [← foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 25 92 (by omega) (by decide) (by decide)]
  have hval_4681 : (((pm_goal_3_faithful.nodes.take 92).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 4681 = (initPM 4680) := by
    rw [foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4681 24 92 (by omega) (by decide) (by decide),
      show pm_goal_3_faithful.nodes.take 24 = pm_goal_3_faithful.nodes.take 23 ++ [{ rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }] from rfl,
      List.foldl_append,
      List.foldl_cons,
      List.foldl_nil,
      applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] } (by decide) (by decide),
      applyNode_fw_float_out pm_goal_3_faithful (((pm_goal_3_faithful.nodes.take 23).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM)) 1 4680 4681 []]
    simp only [foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 23) initPM 4680 (by decide) (by decide)]
  rw [hval_4703, hval_4702, hval_4701, hval_4700, hval_4698, hval_7446, hval_7445, hval_7440, hval_7439, hval_7438, hval_7437, hval_14615, hval_4681]
  try rfl


set_option maxHeartbeats 12000000 in
theorem pm_attn_shard_shapes
    (initSM initPM : Store)
    (h_ss_sm : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    (applyNodeRingAttn_sliding_window pm_goal_3_faithful
       ((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) nR0).shape
      = [2048, 16, 64]
    ∧ (applyNodeRingAttn_sliding_window pm_goal_3_faithful
       ((pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM) nR1).shape
      = [2048, 16, 64] := by
  -- weight equalities
  have hII : InitGoalsHold pm_goal_3_faithful.numRanks initGoals initSM initPM := by
    intro g hg
    exact hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb : ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
    intro g hg hshape
    have hgh := hII g hg
    unfold InitGoalHolds at hgh
    obtain ⟨_, _, hval⟩ := hgh
    rw [hshape] at hval
    simpa [List.map, reconstructWithDim_singleton] using hval
  have h4682 : initSM 4682 = initPM 4682 := hb initGoal_4682 (by decide) rfl
  have h4684 : initSM 4684 = initPM 4684 := hb initGoal_4684 (by decide) rfl
  have h4686 : initSM 4686 = initPM 4686 := hb initGoal_4686 (by decide) rfl
  have h4688 : initSM 4688 = initPM 4688 := hb initGoal_4688 (by decide) rfl
  have h4690 : initSM 4690 = initPM 4690 := hb initGoal_4690 (by decide) rfl
  have h4691 : initSM 4691 = initPM 4691 := hb initGoal_4691 (by decide) rfl
  have h4694 : initSM 4694 = initPM 4694 := hb initGoal_4694 (by decide) rfl
  have h4695 : initSM 4695 = initPM 4695 := hb initGoal_4695 (by decide) rfl
  have h4680 : initSM 4680 = initPM 4680 := by
    have hg := hInit goal_5
      (by unfold goal_3_cut_initGoals goal_3_prereqs; exact List.mem_append_right _ (by simp))
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simpa [goal_5, List.map, reconstructWithDim_singleton] using hval
  -- store <-> prefix-fold bridges
  have bSM4692 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4692
      = denoteGraph_ringAttn sm_goal_3_faithful initSM 4692 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4692 8 (by decide) (by decide)).symm
  have bSM4693 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4693
      = denoteGraph_ringAttn sm_goal_3_faithful initSM 4693 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4693 8 (by decide) (by decide)).symm
  have bSM4689 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4689
      = denoteGraph_ringAttn sm_goal_3_faithful initSM 4689 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3_faithful sm_goal_3_faithful.nodes initSM 4689 8 (by decide) (by decide)).symm
  have bPM7433 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7433 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7433 44 (by decide) (by decide)).symm
  have bPM7434 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7434 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7434 44 (by decide) (by decide)).symm
  have bPM7435 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7435
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7435 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7435 44 (by decide) (by decide)).symm
  have bPM7436 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7436
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7436 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7436 44 (by decide) (by decide)).symm
  have bPM7421 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7421
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7421 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7421 44 (by decide) (by decide)).symm
  have bPM7422 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7422
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 7422 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7422 44 (by decide) (by decide)).symm
  -- corrected Q reconstruction (16 heads), K and V (4 heads)
  have hT16 : ((fw_rotary_embedding (initPM 4691) (initPM 4690)
        (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4684))
        (fw_per_head_linear (fw_rms_norm (initPM 4680) (initPM 4682)) (initPM 4686)) 16 4).1).shape
      = [2 * 2048, 16, 64] :=
    qrot_shape_p3 initPM (h_ss_pm 4680 [4096,1024] (by decide)) (h_ss_pm 4682 [1024] (by decide))
      (h_ss_pm 4684 [16,64,1024] (by decide)) (h_ss_pm 4686 [4,64,1024] (by decide))
  have qproj16 : denoteGraph_ringAttn sm_goal_3_faithful initSM 4692
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3_faithful initPM 7433, denoteGraph_ringAttn pm_goal_3_faithful initPM 7434] := by
    rw [denote_sm_goal_3_faithful_4692, denote_pm_goal_3_qproj_0_r0, denote_pm_goal_3_qproj_0_r1]
    rw [h4680, h4682, h4684, h4686, h4690, h4691]
    rw [show pm_goal_3_faithful.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega) _ hT16).symm
  have kproj := sm_pm_kproj_L0_commute initSM initPM hInit
    (krot_shape_p3 initPM (h_ss_pm 4680 [4096,1024] (by decide)) (h_ss_pm 4682 [1024] (by decide))
      (h_ss_pm 4684 [16,64,1024] (by decide)) (h_ss_pm 4686 [4,64,1024] (by decide)))
  have vproj := sm_pm_vproj_L0_commute initSM initPM hInit
    (ph_shape_p3 initPM 4688 4 (h_ss_pm 4680 [4096,1024] (by decide)) (h_ss_pm 4682 [1024] (by decide))
      (h_ss_pm 4688 [4,64,1024] (by decide)))
  -- store-level q/k/v full hypotheses
  have hq_full : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4692
      = allGatherPrimDimN 0 2 0
          [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433,
           (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434] := by
    rw [bSM4692, bPM7433, bPM7434]; exact qproj16
  have hk_full : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4693
      = allGatherPrimDimN 0 2 0
          [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7435,
           (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7436] := by
    rw [bSM4693, bPM7435, bPM7436]; exact kproj
  have hv_full : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4689
      = allGatherPrimDimN 0 2 0
          [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7421,
           (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7422] := by
    rw [bSM4689, bPM7421, bPM7422]; exact vproj
  -- shapes of SM inputs
  have hSMq_shape : ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4692).shape
      = [4096, 16, 64] := by
    rw [bSM4692, denote_sm_goal_3_faithful_4692]
    exact qrot_shape_p3 initSM (h_ss_sm 4680 [4096,1024] (by decide)) (h_ss_sm 4682 [1024] (by decide))
      (h_ss_sm 4684 [16,64,1024] (by decide)) (h_ss_sm 4686 [4,64,1024] (by decide))
  have hSMk_shape : ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4693).shape
      = [4096, 4, 64] := by
    rw [bSM4693, denote_sm_goal_3_faithful_4693]
    exact krot_shape_p3 initSM (h_ss_sm 4680 [4096,1024] (by decide)) (h_ss_sm 4682 [1024] (by decide))
      (h_ss_sm 4684 [16,64,1024] (by decide)) (h_ss_sm 4686 [4,64,1024] (by decide))
  have hSMv_shape : ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4689).shape
      = [4096, 4, 64] := by
    rw [bSM4689, denote_sm_goal_3_faithful_4689]
    exact ph_shape_p3 initSM 4688 4 (h_ss_sm 4680 [4096,1024] (by decide)) (h_ss_sm 4682 [1024] (by decide))
      (h_ss_sm 4688 [4,64,1024] (by decide))
  have hq_sm : 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4692).shape.length
    rw [hSMq_shape]; decide
  have hk_sm : 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4693).shape.length
    rw [hSMk_shape]; decide
  have hv_sm : 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4689).shape.length
    rw [hSMv_shape]; decide
  -- cu_seqlens equalities
  have hSM4694 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4694 = initSM 4694 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 8) initSM 4694 (by decide) (by decide)
  have hSM4695 : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4695 = initSM 4695 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3_faithful (sm_goal_3_faithful.nodes.take 8) initSM 4695 (by decide) (by decide)
  have hPM4694 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4694 = initPM 4694 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 44) initPM 4694 (by decide) (by decide)
  have hPM4695 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4695 = initPM 4695 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3_faithful (pm_goal_3_faithful.nodes.take 44) initPM 4695 (by decide) (by decide)
  have hcuQ_sm_pm : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 3 0)
      = (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 3 0) := by
    show (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4694
        = (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4694
    rw [hSM4694, hPM4694, h4694]
  have hcuK_sm_pm : (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM (nSM.ins.getD 4 0)
      = (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 4 0) := by
    show (sm_goal_3_faithful.nodes.take 8).foldl (applyNodeRingAttn sm_goal_3_faithful) initSM 4695
        = (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4695
    rw [hSM4695, hPM4695, h4695]
  -- full attention output shape
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 0 0),
                                  (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 1 0),
                                  (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 2 0),
                                  (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 2 0)])
        ((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 3 0))
        ((pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 4 0))
        (nR0.params.getD 0 1) (nR0.params.getD 1 1) (nR0.params.getD 2 1) (nR0.params.getD 3 1)
        (decide (nR0.params.getD 4 0 ≠ 0)) (nR0.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433,
                                    (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, hSMq_shape]; rfl
  -- bridge r1 store take44 -> take45
  have e7433 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7433 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7433 44 45 (by omega) (by decide) (by decide)).symm
  have e7434 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7434 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7434 44 45 (by omega) (by decide) (by decide)).symm
  have e7435 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7435
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7435 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7435 44 45 (by omega) (by decide) (by decide)).symm
  have e7436 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7436
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7436 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7436 44 45 (by omega) (by decide) (by decide)).symm
  have e7421 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7421
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7421 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7421 44 45 (by omega) (by decide) (by decide)).symm
  have e7422 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7422
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 7422 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 7422 44 45 (by omega) (by decide) (by decide)).symm
  have e4694b : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4694
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4694 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4694 44 45 (by omega) (by decide) (by decide)).symm
  have e4695b : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4695
      = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM 4695 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3_faithful pm_goal_3_faithful.nodes initPM 4695 44 45 (by omega) (by decide) (by decide)).symm
  refine ⟨?_, ?_⟩
  · unfold applyNodeRingAttn_sliding_window
    rw [buddy_r0]
    simp only [List.map, List.findIdx?, List.findIdx?.go, if_true, ite_true, eq_self_iff_true,
      Option.getD_some, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add]
    rw [chunkPrimDimN_shape 0 2 _ _ [2 * 2048, 16, 64] hfull_shape (by omega)]
    decide
  · unfold applyNodeRingAttn_sliding_window
    rw [buddy_r1]
    simp only [List.map, List.findIdx?, List.findIdx?.go, if_true, ite_true, if_false, ite_false,
      eq_self_iff_true, Option.getD_some, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add]
    rw [show (nR1.ins.getD 3 0) = (nR0.ins.getD 3 0) from rfl,
        show (nR1.ins.getD 4 0) = (nR0.ins.getD 4 0) from rfl,
        show nR1.params = nR0.params from rfl]
    have B0 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 0 0) = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 0 0) := e7433
    have B1 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 0 0) = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 0 0) := e7434
    have B2 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 1 0) = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 1 0) := e7435
    have B3 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 1 0) = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 1 0) := e7436
    have B4 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 2 0) = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 2 0) := e7421
    have B5 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 2 0) = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR1.ins.getD 2 0) := e7422
    have B6 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 3 0) = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 3 0) := e4694b
    have B7 : (pm_goal_3_faithful.nodes.take 44).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 4 0) = (pm_goal_3_faithful.nodes.take 45).foldl (applyNodeRingAttn pm_goal_3_faithful) initPM (nR0.ins.getD 4 0) := e4695b
    rw [← B0, ← B1, ← B2, ← B3, ← B4, ← B5, ← B6, ← B7]
    rw [chunkPrimDimN_shape 0 2 _ _ [2 * 2048, 16, 64] hfull_shape (by omega)]
    decide

set_option maxHeartbeats 4000000 in
theorem sm_pm_carry_4703_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4703
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 4703 := by
  rw [denote_sm_goal_3_faithful_4703, denote_pm_goal_3_faithful_4703]
  have hattn := sm_pm_attention_L0_commute initSM initPM hSM hPM hInit
  have hII : InitGoalsHold pm_goal_3_faithful.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb : ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
    intro g hg hshape
    have hgh := hII g hg
    unfold InitGoalHolds at hgh
    obtain ⟨_, _, hval⟩ := hgh
    rw [hshape] at hval
    simpa [List.map, reconstructWithDim_singleton] using hval
  have h4699 : initSM 4699 = initPM 4699 := hb initGoal_4699 (by decide) rfl
  have h4680 : initSM 4680 = initPM 4680 := by
    have hg := hInit goal_5
      (by unfold goal_3_cut_initGoals goal_3_prereqs; exact List.mem_append_right _ (by simp))
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simpa [goal_5, List.map, reconstructWithDim_singleton] using hval
  obtain ⟨hsh0, hsh1⟩ := pm_attn_shard_shapes initSM initPM hSM hPM hInit
  simp only [nR0, nR1] at hsh0 hsh1
  rw [show pm_goal_3_faithful.numRanks = 2 from rfl] at hattn ⊢
  rw [hattn]
  rw [carry_view_commute _ _ hsh0 hsh1]
  rw [h4680, h4699]

set_option maxHeartbeats 4000000 in
theorem sm_pm_nl_4708_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    denoteGraph_ringAttn sm_goal_3_faithful initSM 4708
      = denoteGraph_ringAttn pm_goal_3_faithful initPM 4708 := by
  rw [denote_sm_goal_3_faithful_4708, denote_pm_goal_3_faithful_4708]
  rw [sm_pm_carry_4703_commute initSM initPM hSM hPM hInit]
  have hII : InitGoalsHold pm_goal_3_faithful.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb : ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
    intro g hg hshape
    have hgh := hII g hg
    unfold InitGoalHolds at hgh
    obtain ⟨_, _, hval⟩ := hgh
    rw [hshape] at hval
    simpa [List.map, reconstructWithDim_singleton] using hval
  have h4704 : initSM 4704 = initPM 4704 := hb initGoal_4704 (by decide) rfl
  have h4707 : initSM 4707 = initPM 4707 := hb initGoal_4707 (by decide) rfl
  rw [h4704, h4707]

-- Layer-0 router commute (kernel-clean L0 spike, template for L1..L23).
set_option maxHeartbeats 4000000 in
theorem sm_pm_router_commute_L0
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3_faithfulInitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3_faithfulInitEnv)
    (hInit : InitGoalsHold pm_goal_3_faithful.numRanks goal_3_cut_initGoals initSM initPM) :
    (sm_goal_3_faithful_routers initSM).getD 0 (zeroTensor [2 * 2048, 64]) =
      allGatherPrimDimN 0 2 0
        [(pm_goal_3_faithful_routers_r0 initPM).getD 0 (zeroTensor [2048, 64]),
         (pm_goal_3_faithful_routers_r1 initPM).getD 0 (zeroTensor [2048, 64])] := by
  simp only [sm_goal_3_faithful_routers, pm_goal_3_faithful_routers_r0,
    pm_goal_3_faithful_routers_r1, List.getD_cons_zero]
  rw [denote_sm_goal_3_faithful_4710, denote_pm_goal_3_faithful_7483,
      denote_pm_goal_3_faithful_7484, denote_pm_goal_3_faithful_7479,
      denote_pm_goal_3_faithful_7480]
  have hnl := sm_pm_nl_4708_commute initSM initPM hSM hPM hInit
  have hPM4708sh : (denoteGraph_ringAttn pm_goal_3_faithful initPM 4708).shape = [4096, 64] := by
    rw [denote_pm_goal_3_faithful_4708]
    exact nl_sh 4096 1024 64 _ _
      (by rw [rms_sh, denote_pm_goal_3_faithful_4703]
          exact ewadd_eq _ _ [4096,1024] (hPM 4680 [4096,1024] (by decide)) (view_sh _ _))
      (hPM 4707 [64,1024] (by decide))
  have hSM4708sh : (denoteGraph_ringAttn sm_goal_3_faithful initSM 4708).shape = [4096, 64] := by rw [hnl]; exact hPM4708sh
  have hc0sh : (chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm_goal_3_faithful initPM 4708)).shape = [2048, 64] :=
    chunk0_2 0 _ 4096 64 hPM4708sh
  have hc1sh : (chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm_goal_3_faithful initPM 4708)).shape = [2048, 64] :=
    chunk0_2 1 _ 4096 64 hPM4708sh
  rw [show (denoteGraph_ringAttn sm_goal_3_faithful initSM 4708).shape.reverse.head?.getD 1 = 64 from by rw [hSM4708sh]; rfl,
      show (chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm_goal_3_faithful initPM 4708)).shape.reverse.head?.getD 1 = 64 from by rw [hc0sh]; rfl,
      show (chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm_goal_3_faithful initPM 4708)).shape.reverse.head?.getD 1 = 64 from by rw [hc1sh]; rfl]
  exact router_commute_of_nl_eq _ _ hPM4708sh hnl

/-- Per-layer commute (`sm.router_L{k} = allGather0 [pm_r0.router_L{k}, pm_r1.router_L{k}]`).
    L0..L11 use sliding_window attn (shard-local, causal window = 512 ≤ 2048).
    L12..L23 use zigzag ring attn (cross-rank q-gather + broadcast k/v).

    ## Verified reduction roadmap (2026-07-06, Worker E)

    Under the faithful reshape semantics these are all TRUE. The proof of each
    layer `k` reduces, in three graph-independent + one graph-specific step, to a
    single *carry* (residual-stream) equality:

    1.  **Router split (DONE, kernel-clean).** In BOTH graphs the layer-`k`
        norm-linear logits `NL` are computed as a full `[4096, 64]` tensor
        (SM router tids are `sm_goal_3_faithful_routers`, PM shard router tids are
        `pm_goal_3_faithful_routers_r0/_r1`; the layer stride is 54 for the
        sliding-window band L0..L11 and shifts at the L12 zigzag boundary — read
        the tid off the router lists, do not assume a uniform stride.  In both
        graphs the router feeds off `FW_norm_linear` on the *full*
        `[4096, 1024]` rms-norm output — verified: PM does `norm_linear` on the
        AllGather-reconstructed full carry, *then* a `ChunkPrim` splits it into
        the two `[2048, 64]` shards feeding the two per-rank `FW_topk_routing`
        nodes). Hence:
          - SM router  = `(fw_topk_routing NL_SM 8 64).snd.fst`
          - PM r0/r1   = `(fw_topk_routing (chunkPrimDimN 0 2 {0,1} NL_PM) 8 64).snd.fst`
        and `router_commute_of_nl_eq` (above) closes the split GIVEN `NL_SM = NL_PM`.

    2.  **NL equality ⟸ carry equality.** `NL = fw_norm_linear (fw_float
        (fw_rms_norm carry w704)) w707`. The weights `w704 = 4704`, `w707 = 4707`
        are single-`tps` init goals so `initSM = initPM` on them; hence
        `NL_SM = NL_PM ⟺ carry_SM = carry_PM` (congruence).

    3.  **Carry equality (the remaining crux).** `carry_SM`/`carry_PM` are the
        full `[4096, 1024]` residual streams (SM/PM `FW_add` output feeding the
        layer rms-norm; read tids off the graph per layer).
        `carry_k = carry_{k-1} + attn_block_k + moe_block_k`. By induction on `k`
        (base `carry_0` = embedding + attn₀ + moe₀), assuming `carry_{k-1}`
        commutes, the residual block commutes because:
          - `attn_block`: L0..L11 sliding-window (window 512 ≤ shard 2048, so the
            SM full attention = AllGather0 of the two per-shard attentions — the PM
            graph literally does per-shard `FW_attn_sliding_window` then
            `AllGatherPrim`); L12..L23 zigzag ring attn
            (`applyNodeRingAttn_zigzag`).  reshape/linear commute through dim-0
            sharding under faithful reshape (flatten preserves dim-0).
          - `moe_block`: `fw_all2all_moe_gmm_full_split_commute_2` (as in legacy
            `sm_pm_carry_L0_commute`).
          - `swiglu`/`mul`/`add`: row-wise, commute with dim-0 sharding.

    ## Remaining mechanization (per layer, ~200 lines each)
    - three denote-unfold lemmas (SM router tid, PM r0/r1 router tids) reducing
      each `denoteGraph_ringAttn …` to the closed `fw_topk_routing …` form (this
      is the "reduction infra" — bulky `foldl_prefix_eq_full_ringAttn` /
      `foldl_take_split_at_not_written_ringAttn` chains, cf.
      `denote_sm_goal_3_faithful_4675`);
    - the carry-commute recursion (step 3), the mathematical heart, mirroring
      legacy `sm_pm_carry_L{k}_commute` but on the faithful 1866-node PM graph.

    The router-split algebra (step 1) is fully discharged and kernel-clean via
    `router_commute_of_nl_eq`.

    ## Worker F verified findings (2026-07-06) — concrete path for the carry crux

    Graph facts read directly off `sm_goal_3_faithful` / `pm_goal_3_faithful`:

    1.  **L0 carry equality is a FULL-tensor equality, not an allGather.** The PM
        graph computes the layer-0 residual `4703` on both ranks by AllGather-ing
        the two attention shards (`7445, 7446 → 4698 = AllGatherPrim`), then running
        `FW_mix_precision_linear`/`FW_view`/`FW_add` on the *full* `[4096,1024]`
        tensor (replicated per rank). Hence the crux for L0's router is simply
        `denote sm_goal_3_faithful initSM 4703 = denote pm_goal_3_faithful initPM 4703`
        (both `[4096,1024]`). SM router logits `4708 = norm_linear(float(rms_norm(
        multiref 4703, 4704)), 4707)`; PM does the same full `norm_linear`, then a
        `ChunkPrim` splits into `7479, 7480` feeding the per-rank topk `7483, 7484`.
        Per-layer stride: SM carry `4703 + 54k` / logits `4708 + 54k` / router
        `4710 + 54k` for the sliding-window band L0..L11; the stride shifts at the
        L12 zigzag boundary (read tids off the router lists, do NOT assume 54).

    2.  **Carry equality ⟸ attention commute + view/allGather.** Unfolding both
        sides, `4703 = elemwiseAdd (st 4680) (fw_view [4096,1024] (mix_lin (…attn…)
        (st 4699)))`. Under faithful reshape `FW_reshape params → fw_view params`
        (`applyNode_fw_reshape_out`), the SM `reshape;reshape` and PM
        `reshape;reshape;AllGather` differ only by whether the dim-0 flatten happens
        before or after the AllGather. With weight equalities `st4680/st4699 =`
        (single-tps init goals) it reduces to
          `fw_view∘fw_view (SM_full_attn) = AllGather0 [fw_view∘fw_view attn_r0,
                                                        fw_view∘fw_view attn_r1]`,
        i.e. the **attention commute** `SM_full_attn = AllGather0[attn_r0, attn_r1]`
        at `[4096,16,64]` composed with `fw_view_allGather0_commute` (dim-0 flatten
        commutes with allGather0).

    3.  **Attention commute is fully bounded — no legacy-graph re-derivation.** The
        SM L0 attention subgraph (`nodes.take 9`, tids 4680–4696) is byte-identical
        to legacy; the three SM Q/K/V denote-unfolds are already added kernel-clean
        (`denote_sm_goal_3_faithful_4692/4693/4689`). The reconstruction primitives
        `applyNodeRingAttn_sliding_window_singleton` / `_pair_eq_chunk` live in core
        `Denote.lean` (accessible). Only the graph-independent wrappers
        `attn_sw_store_congr`, `applyNodeRingAttn_sliding_window_reconstruction_2_of_
        buddy_pair`, and the value-level shape helpers `ph_shape_p3 / qrot_shape_p3 /
        krot_shape_p3 / fw_attn_varlen_shape_p3` need copying from legacy Pattern_3
        (each ≤ 20 lines, no graph dependence). The PM L0 attention shards sit at
        `pm_goal_3_faithful.nodes.take 44/45` (attn nodes 44/45; Q shards `7433,7434`
        = `ChunkPrim 4692`, K `7435,7436` = `ChunkPrim 4693`, V `7421,7422` =
        `ChunkPrim 4689`); their denote-unfolds mirror the SM ones through the
        interleaved-rank prefix.  For the zigzag band L12..L23 swap
        `applyNodeRingAttn_sliding_window` → `_zigzag` and the reconstruction wrapper
        to `applyNodeRingAttn_zigzag_reconstruction_2_of_buddy_pair`.

    4.  **MoE / swiglu / gate blocks** commute via the already-imported
        `fw_all2all_moe_gmm_full_split_commute_2` + `fw_swiglu_allGather0_commute_2`
        exactly as in legacy `sm_pm_carry_L0_commute` (the PM MoE weights are the
        `ChunkPrim`-split `[32,…]` shards `7487/7488`, `7489/7490` at L0).

    Fast-iteration tip: develop each layer's lemmas in a scratch module that
    `import`s this file (the cached `.olean` gives ~4 s builds vs. ~13 min for the
    full module), then paste the verified block back here. -/
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
