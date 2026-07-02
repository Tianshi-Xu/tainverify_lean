/- # `fw_inner_chunk_ce` sharding along dim 0 (context-parallel)

  This file proves the top-level equivalence lemma used by YOCO Pattern_2:

  ```
  (fw_inner_chunk_ce (allGatherPrimDimN 0 numParts _ xs) w
                     (allGatherPrimDimN 0 numParts _ ys) vocab zScale).snd
    = allGatherPrimDimN 0 numParts 0
        (List.zipWith (fun x y => (fw_inner_chunk_ce x w y vocab zScale).snd) xs ys)
  ```

  Mathematical intuition: `zLosses[l] = zScale * (LogSumExp(logits[l, :]))^2`
  where `logits = fw_linear x w`. LogSumExp only reads row `l` of `logits`,
  and `fw_linear` is row-independent. So if `x_full = concat_row(xs)`, the
  l-th row of `logits_full = fw_linear x_full w` equals the l_local-th row
  of `logits_r = fw_linear (xs r) w` where `r = l / L_shard, l_local = l % L_shard`.
  Hence `zLosses_full[l] = zLosses_r[l_local]`, i.e. `zLosses_full` is
  the `allGather` of the per-shard `zLosses`.

  Written 2026-07-02 as Session A of YOCO Pattern_2 hand-proof (M3).
-/
import denote.Denote
import denote.DenoteMoE
import Mathlib.Data.List.Basic

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote

open TrainVerify.Denote

/-!
### `fw_linear` row-locality: value at `(r, c)` of `fw_linear x w` depends
only on row `r` of `x` (all `h_model` elements) and row `c` of `w`.
-/

/-- `valAt (fw_linear x w) (r * o + c)` unfolded via `fw_linear_is_matmul`. -/
theorem fw_linear_2d_valAt
    (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i])
    (r : Nat) (hr : r < b) (c : Nat) (hc : c < o) :
    valAt (fw_linear x w) (r * o + c) =
      ∑ j ∈ Finset.range i, (valAt x (r * i + j)) * (valAt w (c * i + j)) := by
  rw [fw_linear_is_matmul b i o x w hx hw]
  have hprod : prodShape [b, o] = b * o := by simp [prodShape]
  have hidx_lt : r * o + c < prodShape [b, o] := by
    rw [hprod]
    calc r * o + c < r * o + o := by omega
      _ = (r + 1) * o := by ring
      _ ≤ b * o := Nat.mul_le_mul_right _ hr
  -- Now the goal reads `valAt (Tensor.mkShape [b,o] (k_matmul b o i x w)) (r*o+c) = ...`
  simp only [valAt, Tensor.mkShape, hidx_lt, dif_pos]
  -- Now the goal reads `k_matmul b o i x w ⟨r*o+c, _⟩ = ...`
  unfold k_matmul
  -- outIdx.1 = r * o + c; outIdx.1 / o = r; outIdx.1 % o = c.
  have ho_pos : 0 < o := by omega
  have hdiv : (r * o + c) / o = r := by
    rw [show r * o + c = c + o * r from by ring,
        Nat.add_mul_div_left _ _ ho_pos, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (r * o + c) % o = c := by
    rw [show r * o + c = c + o * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  simp only [hdiv, hmod]
  -- After hdiv/hmod, the k_matmul RHS matches modulo an inline `valAt` unfold.
  -- Rebracket to match.
  apply Finset.sum_congr rfl
  intro j _hj
  rfl

/-!
### The main sharding claim, factored as a row-level identity.
-/

/-- Row-level identity: `fw_linear (allGather xs) w` at row `l`, col `c`
    equals `fw_linear (xs[r]) w` at row `l_local`, col `c`, where
    `r = l / L_shard` and `l_local = l % L_shard`. -/
theorem fw_linear_row_shard
    (numParts L_shard h_model vocab : Nat) (xs : List Tensor) (w : Tensor)
    (hparts : 0 < numParts) (hL : 0 < L_shard) (hh : 0 < h_model) (hv : 0 < vocab)
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [L_shard, h_model])
    (hxs_shape : ∀ r (_ : r < numParts),
        (xs.getD r (zeroTensor [L_shard, h_model])).shape = [L_shard, h_model])
    (hw : w.shape = [vocab, h_model])
    (r : Nat) (hr : r < numParts) (i : Nat) (hi : i < L_shard) (c : Nat) (hc : c < vocab) :
    valAt (fw_linear (allGatherPrimDimN 0 numParts 0 xs) w) ((r * L_shard + i) * vocab + c) =
      valAt (fw_linear (xs.getD r (zeroTensor [L_shard, h_model])) w) (i * vocab + c) := by
  -- Shape facts.
  have hgather_shape : (allGatherPrimDimN 0 numParts 0 xs).shape = [L_shard * numParts, h_model] := by
    have := allGatherPrimDimN_shape 0 numParts xs [L_shard, h_model] hxs_head
    simpa using this
  have hxr_shape : (xs.getD r (zeroTensor [L_shard, h_model])).shape = [L_shard, h_model] :=
    hxs_shape r hr
  have hri_lt : r * L_shard + i < L_shard * numParts := by
    have hsi : r * L_shard + i < (r + 1) * L_shard := by
      calc r * L_shard + i < r * L_shard + L_shard := by omega
        _ = (r + 1) * L_shard := by ring
    calc r * L_shard + i < (r + 1) * L_shard := hsi
      _ ≤ numParts * L_shard := Nat.mul_le_mul_right _ hr
      _ = L_shard * numParts := by ring
  -- Unfold both sides via fw_linear_2d_valAt.
  rw [fw_linear_2d_valAt (L_shard * numParts) h_model vocab _ w hgather_shape hw
        (r * L_shard + i) hri_lt c hc]
  rw [fw_linear_2d_valAt L_shard h_model vocab _ w hxr_shape hw i hi c hc]
  -- Both sums have the same range and identical `valAt w (c * h_model + j)` factors.
  -- Just need `valAt (allGather xs) ((r*L_shard+i)*h_model + j) = valAt xs[r] (i*h_model + j)`.
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  congr 1
  exact allGatherPrimDimN0_valAt numParts L_shard h_model xs hparts hL hh hxs_head hxs_shape
    r hr i hi j hj

/-!
### Now the `xentLogSumExp` row-sharding.
-/

/-- `xentLogSumExp` reads only the `vocab` entries at positions
    `i * vocab + v` for `v ∈ [0, vocab)`. Restated as a lemma so the sum can
    be manipulated by `Finset.sum_congr`. -/
theorem xentLogSumExp_congr_row
    (logits1 logits2 : Tensor) (i1 i2 vocab : Nat)
    (hrow : ∀ v ∈ Finset.range vocab,
      valAt logits1 (i1 * vocab + v) = valAt logits2 (i2 * vocab + v)) :
    xentLogSumExp logits1 i1 vocab = xentLogSumExp logits2 i2 vocab := by
  unfold xentLogSumExp
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  rw [hrow v hv]

/-- Row `l` of `xentLogSumExp` on `fw_linear (allGather xs) w` equals the
    corresponding row on `fw_linear (xs[r]) w`, when reading columns `[0, vocab)`. -/
theorem xentLogSumExp_fw_linear_shard
    (numParts L_shard h_model vocab : Nat) (xs : List Tensor) (w : Tensor)
    (hparts : 0 < numParts) (hL : 0 < L_shard) (hh : 0 < h_model) (hv : 0 < vocab)
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [L_shard, h_model])
    (hxs_shape : ∀ r (_ : r < numParts),
        (xs.getD r (zeroTensor [L_shard, h_model])).shape = [L_shard, h_model])
    (hw : w.shape = [vocab, h_model])
    (r : Nat) (hr : r < numParts) (i : Nat) (hi : i < L_shard) :
    xentLogSumExp (fw_linear (allGatherPrimDimN 0 numParts 0 xs) w) (r * L_shard + i) vocab =
      xentLogSumExp (fw_linear (xs.getD r (zeroTensor [L_shard, h_model])) w) i vocab := by
  apply xentLogSumExp_congr_row
  intro v hvmem
  rw [Finset.mem_range] at hvmem
  exact fw_linear_row_shard numParts L_shard h_model vocab xs w
    hparts hL hh hv hxs_head hxs_shape hw r hr i hi v hvmem

/-!
### Main theorem: `fw_inner_chunk_ce.snd` shards along dim 0.
-/

/-!
### 1D variant of `allGatherPrimDimN0_valAt` (helper).
-/

/-- Value of `allGatherPrimDimN 0 numParts 0 Ws` at index `r * shard + i`,
    when the shards have shape `[shard]` (1D case) and `r < numParts`,
    `i < shard`. -/
theorem allGatherPrimDimN0_valAt_1d
    (numParts shard : Nat) (Ws : List Tensor)
    (hparts : 0 < numParts) (hshard : 0 < shard)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [shard])
    (hWs_shape : ∀ r (_ : r < numParts),
        (Ws.getD r (zeroTensor [shard])).shape = [shard])
    (r : Nat) (hr : r < numParts) (i : Nat) (hi : i < shard) :
    valAt (allGatherPrimDimN 0 numParts 0 Ws) (r * shard + i) =
      valAt (Ws.getD r (zeroTensor [shard])) i := by
  -- Bound the index in the output shape.
  have hri_lt : r * shard + i < shard * numParts := by
    have hsi : r * shard + i < (r + 1) * shard := by
      calc r * shard + i < r * shard + shard := by omega
        _ = (r + 1) * shard := by ring
    calc r * shard + i < (r + 1) * shard := hsi
      _ ≤ numParts * shard := Nat.mul_le_mul_right _ hr
      _ = shard * numParts := by ring
  have hshape_out : (allGatherPrimDimN 0 numParts 0 Ws).shape = [shard * numParts] := by
    have := allGatherPrimDimN_shape 0 numParts Ws [shard] hhead
    simpa using this
  have hidx_lt_prod : r * shard + i <
      prodShape (allGatherPrimDimN 0 numParts 0 Ws).shape := by
    rw [hshape_out]
    show r * shard + i < prodShape [shard * numParts]
    simp only [prodShape, List.foldl, Nat.one_mul]
    exact hri_lt
  have hshard_ne : shard ≠ 0 := Nat.ne_of_gt hshard
  have hfds_ne : shard * numParts * 1 ≠ 0 := by
    rw [Nat.mul_one]
    exact Nat.ne_of_gt (Nat.mul_pos hshard hparts)
  have hpost_ne : (1 : Nat) ≠ 0 := by omega
  -- Unfold via .val of the mkShape.
  have h0 : valAt (allGatherPrimDimN 0 numParts 0 Ws) (r * shard + i) =
      (allGatherPrimDimN 0 numParts 0 Ws).val ⟨r * shard + i, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  -- Precompute list operations on [shard].
  have hgetD0 : (([shard] : List Nat).getD 0 0) = shard := rfl
  have hdrop1 : List.foldl (fun (a b : Nat) => a * b) 1
      (List.drop (0 + 1) ([shard] : List Nat)) = 1 := by
    simp [List.drop, List.foldl]
  have hset : (([shard] : List Nat).set 0 (shard * numParts)) = [shard * numParts] := rfl
  -- Index arithmetic.
  have hidx_lt_fds : r * shard + i < shard * numParts * 1 := by
    rw [Nat.mul_one]; exact hri_lt
  have hdiv_fds : (r * shard + i) / (shard * numParts * 1) = 0 :=
    Nat.div_eq_of_lt hidx_lt_fds
  have hmod_fds : (r * shard + i) % (shard * numParts * 1) = r * shard + i :=
    Nat.mod_eq_of_lt hidx_lt_fds
  have hdiv_1 : (r * shard + i) / 1 = r * shard + i := Nat.div_one _
  have hmod_1 : (r * shard + i) % 1 = 0 := Nat.mod_one _
  have hdiv_shard : (r * shard + i) / shard = r := by
    rw [show r * shard + i = i + shard * r from by ring,
        Nat.add_mul_div_left _ _ hshard, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod_shard : (r * shard + i) % shard = i := by
    rw [show r * shard + i = i + shard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  -- Shape of Ws.getD r.
  have hWr_shape : (Ws.getD r (zeroTensor [shard])).shape = [shard] := hWs_shape r hr
  have hWr_prod : prodShape (Ws.getD r (zeroTensor [shard])).shape = shard := by
    rw [hWr_shape]; simp [prodShape]
  have hidx_lt_Wr : i < prodShape (Ws.getD r (zeroTensor [shard])).shape := by
    rw [hWr_prod]; exact hi
  -- Unfold and simplify.
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead, hgetD0, hdrop1, hset,
    if_neg hshard_ne, if_neg hpost_ne, if_neg hfds_ne]
  rw [hmod_fds, hdiv_fds, hdiv_1, hmod_1, hdiv_shard, hmod_shard]
  simp only [Nat.zero_mul, Nat.zero_add, Nat.mul_one, Nat.add_zero, valAt, hidx_lt_Wr, dif_pos]

/-!
### Main theorem: `fw_inner_chunk_ce.snd` shards along dim 0.
-/

/-- Reconstructing the full x from row-sharded xs and then running
    `fw_inner_chunk_ce` gives the same `.snd` (`zLosses`) as running
    `fw_inner_chunk_ce` on each shard and then `allGather`-ing the results.

    The `y` tensor is **not** used in the `.snd` computation
    (`zLosses[l] = zScale * lse(logits, l, vocab)^2` — no `y` reference),
    so we don't need any hypothesis about `y`. -/
theorem fw_inner_chunk_ce_snd_allGatherDim0_shards
    (numParts L_shard h_model vocab : Nat) (zScale : Scalar)
    (xs : List Tensor) (w y : Tensor)
    (hparts : 0 < numParts) (hL : 0 < L_shard) (hh : 0 < h_model) (hv : 0 < vocab)
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [L_shard, h_model])
    (hxs_shape : ∀ r (_ : r < numParts),
        (xs.getD r (zeroTensor [L_shard, h_model])).shape = [L_shard, h_model])
    (hw : w.shape = [vocab, h_model]) :
    (fw_inner_chunk_ce (allGatherPrimDimN 0 numParts 0 xs) w y vocab zScale).snd =
      allGatherPrimDimN 0 numParts 0
        (List.ofFn (n := numParts) (fun r : Fin numParts =>
          (fw_inner_chunk_ce (xs.getD r.val (zeroTensor [L_shard, h_model])) w y vocab zScale).snd)) := by
  -- Shape of allGather xs.
  have hgather_shape : (allGatherPrimDimN 0 numParts 0 xs).shape = [L_shard * numParts, h_model] := by
    have := allGatherPrimDimN_shape 0 numParts xs [L_shard, h_model] hxs_head
    simpa using this
  -- Shape of LHS.
  have hLHS_shape :
      (fw_inner_chunk_ce (allGatherPrimDimN 0 numParts 0 xs) w y vocab zScale).snd.shape
        = [L_shard * numParts] := by
    apply fw_inner_chunk_ce_snd_shape _ _ _ vocab zScale (L_shard * numParts)
    rw [hgather_shape]; rfl
  -- Per-shard shapes.
  have hpershard_shape : ∀ (r : Fin numParts),
      (fw_inner_chunk_ce (xs.getD r.val (zeroTensor [L_shard, h_model])) w y vocab zScale).snd.shape
        = [L_shard] := by
    intro r
    apply fw_inner_chunk_ce_snd_shape _ _ _ vocab zScale L_shard
    rw [hxs_shape r.val r.isLt]; rfl
  -- Set up pieces list.
  set pieces := List.ofFn (n := numParts) (fun r : Fin numParts =>
      (fw_inner_chunk_ce (xs.getD r.val (zeroTensor [L_shard, h_model])) w y vocab zScale).snd)
    with hpieces_def
  -- head? of pieces.
  have hpieces_head : (pieces.head?.map (fun t => t.shape)).getD [] = [L_shard] := by
    have hlen : pieces.length = numParts := by rw [hpieces_def]; exact List.length_ofFn
    have hpos : 0 < pieces.length := by rw [hlen]; exact hparts
    -- pieces = List.ofFn ..., so pieces[0] = (fw_inner_chunk_ce (xs.getD 0 ...) ...).snd.
    -- Use List.head?_eq_head with hpos: pieces.head? = some (pieces.head hne).
    -- Simpler: since 0 < pieces.length, pieces.head? = some pieces[0].
    have hhead_some : pieces.head? =
        some (fw_inner_chunk_ce (xs.getD (0 : Nat) (zeroTensor [L_shard, h_model])) w y vocab zScale).snd := by
      -- pieces = List.ofFn f, and (List.ofFn f).head? = some (f 0) when n > 0.
      rw [hpieces_def]
      -- List.head?_ofFn is not a standard lemma; use getElem? + List.head?_eq_getElem?.
      rw [List.head?_eq_getElem?]
      rw [List.getElem?_ofFn]
      simp [hparts]
    rw [hhead_some, Option.map_some, Option.getD_some]
    apply fw_inner_chunk_ce_snd_shape _ _ _ vocab zScale L_shard
    rw [hxs_shape 0 hparts]; rfl
  -- Shape of RHS.
  have hRHS_shape : (allGatherPrimDimN 0 numParts 0 pieces).shape = [L_shard * numParts] := by
    have := allGatherPrimDimN_shape 0 numParts pieces [L_shard] hpieces_head
    simpa using this
  -- Shape of pieces.getD r (for the 1D valAt helper hypothesis).
  have hpieces_shape : ∀ r (_ : r < numParts),
      (pieces.getD r (zeroTensor [L_shard])).shape = [L_shard] := by
    intro r hr
    have hget : pieces.getD r (zeroTensor [L_shard]) =
        (fw_inner_chunk_ce (xs.getD r (zeroTensor [L_shard, h_model])) w y vocab zScale).snd := by
      rw [hpieces_def, List.getD_eq_getElem?_getD]
      have hpos : r < (List.ofFn (n := numParts) (fun r' : Fin numParts =>
          (fw_inner_chunk_ce (xs.getD r'.val (zeroTensor [L_shard, h_model])) w y vocab zScale).snd)).length := by
        rw [List.length_ofFn]; exact hr
      rw [List.getElem?_eq_getElem hpos, Option.getD_some, List.getElem_ofFn]
    rw [hget]
    apply fw_inner_chunk_ce_snd_shape _ _ _ vocab zScale L_shard
    rw [hxs_shape r hr]; rfl
  -- Tensor.ext.
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  simp only [prodShape, List.foldl, Nat.one_mul] at hidx
  -- Decompose idx = r * L_shard + i where r = idx / L_shard, i = idx % L_shard.
  set r := idx / L_shard
  set i := idx % L_shard
  have hL_ne : L_shard ≠ 0 := Nat.ne_of_gt hL
  have hr_lt : r < numParts := by
    show idx / L_shard < numParts
    rw [Nat.div_lt_iff_lt_mul hL]
    calc idx < L_shard * numParts := hidx
      _ = numParts * L_shard := by ring
  have hi_lt : i < L_shard := Nat.mod_lt _ hL
  have hidx_eq : idx = r * L_shard + i := by
    show idx = idx / L_shard * L_shard + idx % L_shard
    have h1 := Nat.mod_add_div idx L_shard  -- idx % L_shard + L_shard * (idx / L_shard) = idx
    have h2 : L_shard * (idx / L_shard) = idx / L_shard * L_shard := by ring
    linarith
  -- LHS value.
  have hidx_prod : idx < prodShape [L_shard * numParts] := by
    simp [prodShape]; exact hidx
  have hLHS_val_expr :
      valAt (fw_inner_chunk_ce (allGatherPrimDimN 0 numParts 0 xs) w y vocab zScale).snd idx
        = zScale * (xentLogSumExp
            (fw_linear (allGatherPrimDimN 0 numParts 0 xs) w) idx vocab) ^ 2 := by
    -- The .snd of fw_inner_chunk_ce x w y vocab zScale is
    --   Tensor.mkShape [x.shape.head?.getD 0] (fun outIdx => zScale * lseAt outIdx.1 ^ 2)
    -- where lseAt l = xentLogSumExp (fw_linear x w) l vocab.
    -- After substituting x = allGather xs (shape [L_shard*numParts, h]), head?.getD 0 = L_shard*numParts.
    have hgetD : ((allGatherPrimDimN 0 numParts 0 xs).shape.head?).getD 0 = L_shard * numParts := by
      rw [hgather_shape]; rfl
    have hidx_prod' : idx < prodShape [L_shard * numParts] := hidx_prod
    -- Directly show: (fw_inner_chunk_ce ...).snd = Tensor.mkShape [L_shard*numParts] (fun k => zScale * lseAt k.1 ^ 2)
    show valAt (Tensor.mkShape [((allGatherPrimDimN 0 numParts 0 xs).shape.head?).getD 0]
          (fun outIdx => zScale * (xentLogSumExp
            (fw_linear (allGatherPrimDimN 0 numParts 0 xs) w) outIdx.1 vocab) ^ 2)) idx
      = zScale * (xentLogSumExp
          (fw_linear (allGatherPrimDimN 0 numParts 0 xs) w) idx vocab) ^ 2
    rw [hgetD]
    simp only [valAt, Tensor.mkShape, hidx_prod', dif_pos]
  -- RHS value via allGatherPrimDimN0_valAt_1d.
  have hRHS_val_expr :
      valAt (allGatherPrimDimN 0 numParts 0 pieces) idx =
      valAt (pieces.getD r (zeroTensor [L_shard])) i := by
    have := allGatherPrimDimN0_valAt_1d numParts L_shard pieces hparts hL
      hpieces_head hpieces_shape r hr_lt i hi_lt
    rw [hidx_eq]; exact this
  -- pieces.getD r = (fw_inner_chunk_ce (xs.getD r zero) w y vocab zScale).snd.
  have hpiece_r :
      pieces.getD r (zeroTensor [L_shard]) =
      (fw_inner_chunk_ce (xs.getD r (zeroTensor [L_shard, h_model])) w y vocab zScale).snd := by
    rw [hpieces_def, List.getD_eq_getElem?_getD]
    have hpos : r < (List.ofFn (n := numParts) (fun r' : Fin numParts =>
        (fw_inner_chunk_ce (xs.getD r'.val (zeroTensor [L_shard, h_model])) w y vocab zScale).snd)).length := by
      rw [List.length_ofFn]; exact hr_lt
    rw [List.getElem?_eq_getElem hpos, Option.getD_some, List.getElem_ofFn]
  -- Per-shard's .snd value at i.
  have hpiece_val :
      valAt (pieces.getD r (zeroTensor [L_shard])) i =
      zScale * (xentLogSumExp
        (fw_linear (xs.getD r (zeroTensor [L_shard, h_model])) w) i vocab) ^ 2 := by
    rw [hpiece_r]
    have hgetD_r : ((xs.getD r (zeroTensor [L_shard, h_model])).shape.head?).getD 0 = L_shard := by
      rw [hxs_shape r hr_lt]; rfl
    have hi_prod : i < prodShape [L_shard] := by simp [prodShape]; exact hi_lt
    show valAt (Tensor.mkShape [((xs.getD r (zeroTensor [L_shard, h_model])).shape.head?).getD 0]
          (fun outIdx => zScale * (xentLogSumExp
            (fw_linear (xs.getD r (zeroTensor [L_shard, h_model])) w) outIdx.1 vocab) ^ 2)) i
      = zScale * (xentLogSumExp
          (fw_linear (xs.getD r (zeroTensor [L_shard, h_model])) w) i vocab) ^ 2
    rw [hgetD_r]
    simp only [valAt, Tensor.mkShape, hi_prod, dif_pos]
  -- Both sides already in `valAt` form from Tensor.ext (which gives .val equal, but we
  -- proved everything in valAt terms). Chain the equalities:
  rw [hLHS_val_expr, hRHS_val_expr, hpiece_val]
  -- Now: zScale * lse(fw_linear full)^2 at idx = zScale * lse(fw_linear shard_r)^2 at i.
  -- Apply xentLogSumExp_fw_linear_shard.
  rw [hidx_eq]
  congr 1
  congr 1
  exact xentLogSumExp_fw_linear_shard numParts L_shard h_model vocab xs w
    hparts hL hh hv hxs_head hxs_shape hw r hr_lt i hi_lt

end TrainVerify.Denote
