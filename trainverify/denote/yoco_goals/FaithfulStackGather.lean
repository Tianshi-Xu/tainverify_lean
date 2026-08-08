/- Common faithful CP2 unshuffle and stack/gather assembly lemmas. -/
import denote.yoco_goals.ZigzagLayoutRel

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-- Ordinary two-rank lineage used by the pre-zigzag half of Goal 3/4. -/
structure Ordinary2Rel (full rank0 rank1 : Tensor)
    (fullShape shardShape : Shape) : Prop where
  full_value : full = allGatherPrimDimN 0 2 0 [rank0, rank1]
  full_shape : full.shape = fullShape
  rank0_shape : rank0.shape = shardShape
  rank1_shape : rank1.shape = shardShape

-- The extensional proof normalizes both three-dimensional index formulas.
set_option maxHeartbeats 1600000 in
/-- **Lemma B (generic)**: stack-gather commute for shard shape `[2048, 64]`. -/
theorem stack_allGather_commute_generic_2048_64
    (as bs : List Tensor) (hlen : as.length = bs.length) (hne : as ≠ [])
    (hAs : ∀ a ∈ as, a.shape = [2048, 64]) (hBs : ∀ b ∈ bs, b.shape = [2048, 64]) :
    fw_stack (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs)
      = allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs] := by
  -- Setup: shapes.
  have hbs_ne : bs ≠ [] := by
    intro h; apply hne
    have : bs.length = 0 := by rw [h]; rfl
    exact List.length_eq_zero_iff.mp (hlen.trans this)
  have h_as_pos : 0 < as.length := List.length_pos_of_ne_nil hne
  have h_bs_pos : 0 < bs.length := List.length_pos_of_ne_nil hbs_ne
  set N := as.length with hN_def
  have hbs_len : bs.length = N := hlen.symm
  -- Zipped list has length N.
  set zL := List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs with hzL_def
  have hzL_len : zL.length = N := by rw [hzL_def]; rw [List.length_zipWith, hbs_len]; omega
  -- Shard shapes.
  have hAgather : ∀ a b : Tensor, a.shape = [2048, 64] → b.shape = [2048, 64] →
      (allGatherPrimDimN 0 2 0 [a, b]).shape = [4096, 64] := by
    intro a b ha hb
    have hhead : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [2048, 64] := by
      simp [ha]
    rw [allGatherPrimDimN_shape 0 2 [a, b] [2048, 64] hhead]
    simp [List.set, List.getD]
  -- Every element of zL has shape [4096, 64] — use getElem-based reasoning.
  -- Avoid dependent-type rewriting issues by working with List.getElem_zipWith directly.
  have hzL_elem_shape : ∀ (i : Nat) (hi_z : i < zL.length), (zL[i]'hi_z).shape = [4096, 64] := by
    intro i hi_z
    have hi_as : i < as.length := by rw [hzL_len] at hi_z; omega
    have hi_bs : i < bs.length := by rw [hbs_len]; omega
    have h_getElem_eq :
        (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs)[i]'
        (by rw [List.length_zipWith]; omega) =
        allGatherPrimDimN 0 2 0 [as[i]'hi_as, bs[i]'hi_bs] := by
      simp [List.getElem_zipWith]
    -- Reveal zL as zipWith via `show`, then apply eq.
    show ((List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs)[i]'hi_z).shape
        = [4096, 64]
    rw [h_getElem_eq]
    exact hAgather _ _ (hAs _ (List.getElem_mem hi_as)) (hBs _ (List.getElem_mem hi_bs))
  -- head shape of zL: unfold via case-analysis on as & bs (both non-empty).
  have hzL_head : (zL.head?.map (fun t => t.shape)).getD [] = [4096, 64] := by
    rw [hzL_def]
    cases as_lc : as with
    | nil => exact absurd as_lc hne
    | cons a₀ as' =>
      cases bs_lc : bs with
      | nil =>
        exfalso
        rw [bs_lc, hN_def, as_lc] at hlen
        simp at hlen
      | cons b₀ bs' =>
        simp only [List.zipWith, List.head?, Option.map_some, Option.getD_some]
        have ha₀ : a₀.shape = [2048, 64] := hAs a₀ (by rw [as_lc]; exact List.mem_cons_self ..)
        have hb₀ : b₀.shape = [2048, 64] := hBs b₀ (by rw [bs_lc]; exact List.mem_cons_self ..)
        exact hAgather a₀ b₀ ha₀ hb₀
  -- fw_stack zL has shape [N, 4096, 64].
  have hLHS_shape : (fw_stack zL).shape = N :: [4096, 64] := by
    rw [fw_stack_shape zL [4096, 64] hzL_head, hzL_len]
  -- as head shape.
  have has_head : (as.head?.map (fun t => t.shape)).getD [] = [2048, 64] := by
    rcases has_lc : as with _ | ⟨h, t⟩
    · exact absurd has_lc hne
    · simp only [List.head?, Option.map_some, Option.getD_some]
      exact hAs h (by rw [has_lc]; exact List.mem_cons_self ..)
  have hbs_head : (bs.head?.map (fun t => t.shape)).getD [] = [2048, 64] := by
    rcases hbs_lc : bs with _ | ⟨h, t⟩
    · exact absurd hbs_lc hbs_ne
    · simp only [List.head?, Option.map_some, Option.getD_some]
      exact hBs h (by rw [hbs_lc]; exact List.mem_cons_self ..)
  have hAs_stack_shape : (fw_stack as).shape = N :: [2048, 64] := by
    rw [fw_stack_shape as [2048, 64] has_head]
  have hBs_stack_shape : (fw_stack bs).shape = N :: [2048, 64] := by
    rw [fw_stack_shape bs [2048, 64] hbs_head, hbs_len]
  -- RHS shape.
  have hRHS_head : (([fw_stack as, fw_stack bs] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = N :: [2048, 64] := by
    simp [hAs_stack_shape]
  have hRHS_shape : (allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs]).shape
      = [N, 4096, 64] := by
    rw [allGatherPrimDimN_shape 1 2 _ (N :: [2048, 64]) hRHS_head]
    simp [List.set, List.getD]
  -- Now use Tensor.ext.
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    -- Both shapes are [N, 4096, 64]. idx < N * 4096 * 64 = N * 262144.
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < N * 262144 := by
      simp only [prodShape, List.foldl_cons, List.foldl_nil] at hidx
      omega
    -- Decompose idx = layer * 262144 + local (row * 64 + col), then row = r * 2048 + jL.
    set layer := idx / 262144 with hlayer_def
    set local' := idx % 262144 with hlocal_def
    have hlayer_lt : layer < N := by
      rw [hlayer_def]
      exact Nat.div_lt_of_lt_mul (by linarith [hidx_bound])
    have hlocal_lt : local' < 262144 := by rw [hlocal_def]; omega
    have hidx_eq : idx = layer * 262144 + local' := by
      rw [hlayer_def, hlocal_def]; omega
    set row := local' / 64 with hrow_def
    set col := local' % 64 with hcol_def
    have hrow_lt : row < 4096 := by rw [hrow_def]; omega
    have hcol_lt : col < 64 := by rw [hcol_def]; omega
    have hlocal_eq : local' = row * 64 + col := by rw [hrow_def, hcol_def]; omega
    set r := row / 2048 with hr_def
    set jL := row % 2048 with hjL_def
    have hr_lt : r < 2 := by rw [hr_def]; omega
    have hjL_lt : jL < 2048 := by rw [hjL_def]; omega
    have hrow_eq : row = r * 2048 + jL := by rw [hr_def, hjL_def]; omega
    -- LHS = valAt (fw_stack zL) idx = valAt (zL[layer]) local'.
    -- Unfold fw_stack.
    have hLHS_eq : valAt (fw_stack zL) idx =
        valAt (zL.getD layer (zeroTensor [4096, 64])) local' := by
      have hidx_prod : idx < prodShape (fw_stack zL).shape := by
        rw [hLHS_shape]
        simp only [prodShape, List.foldl_cons, List.foldl_nil]
        linarith [hidx_bound]
      rw [valAt_of_lt _ _ hidx_prod]
      unfold fw_stack
      simp only [Tensor.mkShape, hzL_head]
      -- shardSize = 262144.
      have hshardSize : prodShape [4096, 64] = 262144 := by decide
      -- Goal: fw_stack's mkShape val at idx = valAt (zL.getD (idx/shardSize)) (idx%shardSize).
      -- After unfold, the expression matches with shardSize computed.
      simp only [hshardSize]
      -- Now the r,localIdx match. Rewrite idx / 262144 = layer, idx % 262144 = local'.
      rw [show idx / 262144 = layer from rfl, show idx % 262144 = local' from rfl]
      rfl
    rw [hLHS_eq]
    -- Now LHS = valAt (zL[layer]) local' = valAt (allGather_0 [as[layer], bs[layer]]) local'.
    have hzL_getD_layer : zL.getD layer (zeroTensor [4096, 64]) =
        allGatherPrimDimN 0 2 0 [as.getD layer (zeroTensor [2048, 64]),
                                 bs.getD layer (zeroTensor [2048, 64])] := by
      rw [hzL_def]
      -- List.zipWith f as bs .getD layer default
      have h_layer_as : layer < as.length := hlayer_lt
      have h_layer_bs : layer < bs.length := by rw [hbs_len]; exact hlayer_lt
      have has_getD : as.getD layer (zeroTensor [2048, 64]) = as[layer]'h_layer_as := by
        simp [List.getD, List.getElem?_eq_getElem h_layer_as]
      have hbs_getD : bs.getD layer (zeroTensor [2048, 64]) = bs[layer]'h_layer_bs := by
        simp [List.getD, List.getElem?_eq_getElem h_layer_bs]
      rw [has_getD, hbs_getD]
      -- List.zipWith f as bs [layer] = f as[layer] bs[layer].
      have hzip_getD : (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs).getD
          layer (zeroTensor [4096, 64])
          = allGatherPrimDimN 0 2 0 [as[layer]'h_layer_as, bs[layer]'h_layer_bs] := by
        have hzip_len : (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b]) as bs).length
            = as.length := by rw [List.length_zipWith]; omega
        have h_layer_zip : layer < (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b])
            as bs).length := by rw [hzip_len]; exact hlayer_lt
        simp [List.getD, List.getElem?_eq_getElem h_layer_zip,
              List.getElem_zipWith]
      exact hzip_getD
    rw [hzL_getD_layer]
    -- Now LHS = valAt (allGather_0 [as[layer], bs[layer]]) local'.
    set a_l := as.getD layer (zeroTensor [2048, 64]) with ha_l_def
    set b_l := bs.getD layer (zeroTensor [2048, 64]) with hb_l_def
    have ha_l_shape : a_l.shape = [2048, 64] := by
      rw [ha_l_def]
      have h_layer_as : layer < as.length := hlayer_lt
      have has_getD : as.getD layer (zeroTensor [2048, 64]) = as[layer]'h_layer_as := by
        simp [List.getD, List.getElem?_eq_getElem h_layer_as]
      rw [has_getD]
      exact hAs (as[layer]'h_layer_as) (List.getElem_mem h_layer_as)
    have hb_l_shape : b_l.shape = [2048, 64] := by
      rw [hb_l_def]
      have h_layer_bs : layer < bs.length := by rw [hbs_len]; exact hlayer_lt
      have hbs_getD : bs.getD layer (zeroTensor [2048, 64]) = bs[layer]'h_layer_bs := by
        simp [List.getD, List.getElem?_eq_getElem h_layer_bs]
      rw [hbs_getD]
      exact hBs (bs[layer]'h_layer_bs) (List.getElem_mem h_layer_bs)
    have hab_head : (([a_l, b_l] : List Tensor).head?.map (fun t => t.shape)).getD []
        = [2048, 64] := by simp [ha_l_shape]
    rw [hlocal_eq]
    have hLHS_val := allGatherPrimDimN0_valAt 2 2048 64 [a_l, b_l]
      (by omega) (by omega) (by omega) hab_head
      (by intro r' hr'; rcases (by omega : r' = 0 ∨ r' = 1) with h | h <;> rw [h] <;>
          simp [List.getD, ha_l_shape, hb_l_shape])
      r hr_lt jL hjL_lt col hcol_lt
    -- Need to convert local' = row * 64 + col with row = r * 2048 + jL to (r*2048+jL)*64+col.
    rw [hrow_eq]
    rw [hLHS_val]
    -- Now LHS = valAt ([a_l, b_l].getD r ...) (jL * 64 + col).
    -- RHS side: unfold allGatherPrimDimN by expanding via valAt_of_lt.
    have hidx_prod_rhs : idx < prodShape (allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs]).shape := by
      rw [hRHS_shape]
      simp only [prodShape, List.foldl_cons, List.foldl_nil]
      linarith [hidx_bound]
    rw [valAt_of_lt _ _ hidx_prod_rhs]
    unfold allGatherPrimDimN
    simp only [Tensor.mkShape, hRHS_head]
    -- Simplify shape lookups and postStride to concrete numbers.
    have h_getD_1 : ([N, 2048, 64] : List Nat).getD 1 0 = 2048 := by rfl
    have h_drop_2 : List.drop (1 + 1) ([N, 2048, 64] : List Nat) = [64] := by rfl
    have h_foldl_64 : List.foldl (fun x1 x2 => x1 * x2) 1 ([64] : List Nat) = 64 := by rfl
    simp only [h_getD_1, h_drop_2, h_foldl_64]
    -- Simplify if conditions.
    simp only [show (2048 : Nat) = 0 ↔ False by decide, show (64 : Nat) = 0 ↔ False by decide,
               show (2048 * 2 * 64 : Nat) = 0 ↔ False by decide,
               if_false, iff_false, ↓reduceIte]
    -- Compute: 2048 * 2 * 64 = 262144; 2048 * 64 = 131072.
    show valAt ([a_l, b_l].getD r (zeroTensor [2048, 64])) (jL * 64 + col) =
         valAt ([fw_stack as, fw_stack bs].getD (idx % 262144 / 64 / 2048)
                  (zeroTensor [N, 2048, 64]))
              (idx / 262144 * 131072 + idx % 262144 / 64 % 2048 * 64 + idx % 262144 % 64)
    -- Rewrite: idx % 262144 = local', local' / 64 = row, local' % 64 = col,
    -- idx / 262144 = layer, row / 2048 = r, row % 2048 = jL.
    rw [show idx % 262144 = local' from rfl,
        show idx / 262144 = layer from rfl,
        show local' / 64 = row from rfl,
        show local' % 64 = col from rfl,
        show row / 2048 = r from rfl,
        show row % 2048 = jL from rfl]
    -- Now: valAt (list.getD r) (jL*64+col) = valAt (list.getD r) (layer*131072 + jL*64 + col)
    -- where LHS list is [a_l, b_l], RHS list is [fw_stack as, fw_stack bs].
    -- Case-split on r ∈ {0, 1}. In each case:
    --   * LHS getD selects a_l (or b_l).
    --   * RHS getD selects fw_stack as (or fw_stack bs).
    --   * fw_stack.valAt(layer*131072 + jL*64 + col) reduces to (as[layer] or bs[layer]).valAt(jL*64+col).
    -- Helper: fw_stack xs .valAt (layer * 131072 + local) = xs[layer].valAt(local) for shard [2048,64].
    have hfs_valAt : ∀ (xs : List Tensor) (h_head : (xs.head?.map (fun t => t.shape)).getD [] = [2048, 64])
        (h_layer_lt : layer < xs.length),
        valAt (fw_stack xs) (layer * 131072 + jL * 64 + col) =
        valAt (xs.getD layer (zeroTensor [2048, 64])) (jL * 64 + col) := by
      intro xs h_head h_layer_lt
      have h_shape : (fw_stack xs).shape = xs.length :: [2048, 64] :=
        fw_stack_shape xs [2048, 64] h_head
      have h_prod : layer * 131072 + jL * 64 + col < prodShape (fw_stack xs).shape := by
        rw [h_shape]
        simp only [prodShape, List.foldl_cons, List.foldl_nil]
        -- xs.length * 131072 > layer * 131072 + jL * 64 + col.
        have : layer * 131072 + jL * 64 + col < xs.length * 131072 := by
          have h1 : jL * 64 + col < 131072 := by nlinarith [hjL_lt, hcol_lt]
          calc layer * 131072 + jL * 64 + col < layer * 131072 + 131072 := by omega
            _ = (layer + 1) * 131072 := by ring
            _ ≤ xs.length * 131072 := by
              apply Nat.mul_le_mul_right
              omega
        linarith [this]
      rw [valAt_of_lt _ _ h_prod]
      unfold fw_stack
      simp only [Tensor.mkShape, h_head]
      -- shardSize = prodShape [2048, 64] = 131072
      have hshard : prodShape ([2048, 64] : Shape) = 131072 := by decide
      simp only [hshard, show (131072 : Nat) = 0 ↔ False by decide, if_false, ↓reduceIte, iff_false]
      have hjLcol : jL * 64 + col < 131072 := by nlinarith [hjL_lt, hcol_lt]
      have hdiv : (layer * 131072 + jL * 64 + col) / 131072 = layer := by omega
      have hmod : (layer * 131072 + jL * 64 + col) % 131072 = jL * 64 + col := by omega
      rw [hdiv, hmod]
    -- Apply hfs_valAt to as/bs based on r.
    have h_layer_lt_as : layer < as.length := hlayer_lt
    have h_layer_lt_bs : layer < bs.length := by rw [hbs_len]; exact hlayer_lt
    rcases (by omega : r = 0 ∨ r = 1) with hr_eq | hr_eq
    · -- r = 0.
      rw [hr_eq]
      show valAt a_l (jL * 64 + col) =
           valAt (fw_stack as) (layer * 131072 + jL * 64 + col)
      rw [hfs_valAt as has_head h_layer_lt_as]
    · -- r = 1.
      rw [hr_eq]
      show valAt b_l (jL * 64 + col) =
           valAt (fw_stack bs) (layer * 131072 + jL * 64 + col)
      rw [hfs_valAt bs hbs_head h_layer_lt_bs]

end
end TrainVerify.Denote.GeneratedPatterns
