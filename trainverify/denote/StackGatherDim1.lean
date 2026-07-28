/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.Denote

/-!
# `FW_stack` against a two-rank dim-0 gather

The final two top-level goals of the YOCO-MoE graph (`4675` / `4676`) stack the
24 per-layer routing tensors. On the single-machine side each member is the full
`[L*2, H]` tensor and the stack is `[24, L*2, H]`. On the parallel side each rank
stacks its own `[L, H]` shards into `[24, L, H]`, and the goal's `AllGatherPrim`
puts the two stacks back together along **dim 1**, not dim 0.

So the obligation is the commutation

```
fw_stack [gather₀(a₀,b₀), …, gather₀(a₂₃,b₂₃)]
  = gather₁ (fw_stack [a₀…a₂₃]) (fw_stack [b₀…b₂₃])
```

which holds because both sides read the same element at every index: the layer
selects the stack member, and within a member the row split is the ordinary dim-0
one. The proof below is index arithmetic, stated for a general member count.
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote

noncomputable section

/-- Value of a `fw_stack` over uniformly-shaped members, at a decomposed index. -/
theorem fw_stack_valAt_2d (xs : List Tensor) (rows cols : Nat)
    (hrows : 0 < rows) (hcols : 0 < cols)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [rows, cols])
    (n : Nat) (hn : n < xs.length) (i : Nat) (hi : i < rows * cols) :
    valAt (fw_stack xs) (n * (rows * cols) + i) =
      valAt (xs.getD n (zeroTensor [rows, cols])) i := by
  have hsize : prodShape [rows, cols] = rows * cols := by
    simp [prodShape]
  have hlt : n * (rows * cols) + i < prodShape (xs.length :: [rows, cols]) := by
    have hp : prodShape (xs.length :: [rows, cols]) = xs.length * (rows * cols) := by
      simp [prodShape]; ring
    rw [hp]
    calc n * (rows * cols) + i < n * (rows * cols) + rows * cols := by omega
      _ = (n + 1) * (rows * cols) := by ring
      _ ≤ xs.length * (rows * cols) := Nat.mul_le_mul_right _ hn
  have hpos : 0 < rows * cols := Nat.mul_pos hrows hcols
  have hdiv : (n * (rows * cols) + i) / (rows * cols) = n := by
    rw [show n * (rows * cols) + i = i + (rows * cols) * n from by ring,
      Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod : (n * (rows * cols) + i) % (rows * cols) = i := by
    rw [show n * (rows * cols) + i = i + (rows * cols) * n from by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  unfold fw_stack
  rw [hhead]
  rw [valAt_of_lt _ _ (by simpa [Tensor.mkShape] using hlt)]
  simp only [Tensor.mkShape, hsize, hpos.ne', hdiv, hmod, if_false, ite_false,
    List.getD_eq_getElem?_getD]

/-- Value of a two-rank **dim-1** gather over `[n, rows, cols]` shards. -/
theorem allGatherPrimDimN1_valAt_3D
    (n rows cols : Nat) (Ws : List Tensor)
    (hn : 0 < n) (hrows : 0 < rows) (hcols : 0 < cols)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [n, rows, cols])
    (r : Nat) (hr : r < 2) (layer : Nat) (hlayer : layer < n)
    (i : Nat) (hi : i < rows) (k : Nat) (hk : k < cols) :
    valAt (allGatherPrimDimN 1 2 0 Ws)
        (layer * (rows * 2 * cols) + ((r * rows + i) * cols + k)) =
      valAt (Ws.getD r (zeroTensor [n, rows, cols]))
        (layer * (rows * cols) + (i * cols + k)) := by
  have hrc : 0 < rows * cols := Nat.mul_pos hrows hcols
  have hfd : 0 < rows * 2 * cols := by positivity
  have hrowsne : rows ≠ 0 := hrows.ne'
  have hcolsne : cols ≠ 0 := hcols.ne'
  have hfdne : rows * 2 * cols ≠ 0 := hfd.ne'
  have hinner : (r * rows + i) * cols + k < rows * 2 * cols := by
    have : r * rows + i < rows * 2 := by
      have : r * rows + i < (r + 1) * rows := by nlinarith
      calc r * rows + i < (r + 1) * rows := this
        _ ≤ 2 * rows := Nat.mul_le_mul_right _ (by omega)
        _ = rows * 2 := by ring
    calc (r * rows + i) * cols + k < (r * rows + i) * cols + cols := by omega
      _ = (r * rows + i + 1) * cols := by ring
      _ ≤ (rows * 2) * cols := Nat.mul_le_mul_right _ (by omega)
      _ = rows * 2 * cols := by ring
  have hidxLt : layer * (rows * 2 * cols) + ((r * rows + i) * cols + k) <
      n * (rows * 2 * cols) := by
    calc layer * (rows * 2 * cols) + ((r * rows + i) * cols + k)
        < layer * (rows * 2 * cols) + rows * 2 * cols := by omega
      _ = (layer + 1) * (rows * 2 * cols) := by ring
      _ ≤ n * (rows * 2 * cols) := Nat.mul_le_mul_right _ hlayer
  have hdivFd : (layer * (rows * 2 * cols) + ((r * rows + i) * cols + k)) /
      (rows * 2 * cols) = layer := by
    rw [show layer * (rows * 2 * cols) + ((r * rows + i) * cols + k)
        = ((r * rows + i) * cols + k) + (rows * 2 * cols) * layer from by ring,
      Nat.add_mul_div_left _ _ hfd, Nat.div_eq_of_lt hinner, Nat.zero_add]
  have hmodFd : (layer * (rows * 2 * cols) + ((r * rows + i) * cols + k)) %
      (rows * 2 * cols) = (r * rows + i) * cols + k := by
    rw [show layer * (rows * 2 * cols) + ((r * rows + i) * cols + k)
        = ((r * rows + i) * cols + k) + (rows * 2 * cols) * layer from by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hinner]
  have hdivPost : ((r * rows + i) * cols + k) / cols = r * rows + i := by
    rw [show (r * rows + i) * cols + k = k + cols * (r * rows + i) from by ring,
      Nat.add_mul_div_left _ _ hcols, Nat.div_eq_of_lt hk, Nat.zero_add]
  have hmodPost : ((r * rows + i) * cols + k) % cols = k := by
    rw [show (r * rows + i) * cols + k = k + cols * (r * rows + i) from by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  have hdivRows : (r * rows + i) / rows = r := by
    rw [show r * rows + i = i + rows * r from by ring,
      Nat.add_mul_div_left _ _ hrows, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmodRows : (r * rows + i) % rows = i := by
    rw [show r * rows + i = i + rows * r from by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  unfold allGatherPrimDimN
  rw [hhead]
  rw [valAt_of_lt _ _ (by
    simp only [Tensor.mkShape, hhead, List.set, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, prodShape, List.foldl, Nat.one_mul]
    calc layer * (rows * 2 * cols) + ((r * rows + i) * cols + k)
        < n * (rows * 2 * cols) := hidxLt
      _ = n * (rows * 2) * cols := by ring)]
  simp only [Tensor.mkShape, hhead, List.set, List.getD, List.drop, List.foldl,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.one_mul, hfdne, hcolsne, hrowsne, if_false, ite_false]
  rw [hdivFd, hmodFd, hdivPost, hmodPost, hdivRows, hmodRows]
  congr 1
  ring

/-- Shape of a `fw_stack` over uniformly-shaped 2-D members. -/
theorem fw_stack_shape_2d (xs : List Tensor) (rows cols : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [rows, cols]) :
    (fw_stack xs).shape = [xs.length, rows, cols] :=
  fw_stack_shape xs [rows, cols] hhead

/-- Stacking commutes with a two-rank dim-0 gather, turning it into a dim-1 gather.

`as`/`bs` are the per-rank shard lists (`n` members each, every member
`[rows, cols]`); `fulls` is the list of their dim-0 gathers. Stacking the fulls
gives the same tensor as gathering the two stacks along dim 1. -/
theorem fw_stack_allGather0_eq_allGather1_stack
    (as bs fulls : List Tensor) (n rows cols : Nat)
    (hrows : 0 < rows) (hcols : 0 < cols) (hn : 0 < n)
    (hlenA : as.length = n) (hlenB : bs.length = n) (hlenF : fulls.length = n)
    (hA : ∀ k (_ : k < n), (as.getD k (zeroTensor [rows, cols])).shape = [rows, cols])
    (hB : ∀ k (_ : k < n), (bs.getD k (zeroTensor [rows, cols])).shape = [rows, cols])
    (hF : ∀ k (_ : k < n), fulls.getD k (zeroTensor [rows * 2, cols]) =
      allGatherPrimDimN 0 2 0
        [as.getD k (zeroTensor [rows, cols]), bs.getD k (zeroTensor [rows, cols])]) :
    fw_stack fulls =
      allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs] := by
  -- Head shapes of the three lists.
  have hheadA : (as.head?.map (fun t => t.shape)).getD [] = [rows, cols] := by
    have hpos : 0 < as.length := by rw [hlenA]; exact hn
    have h0 := hA 0 hn
    rw [List.head?_eq_getElem? , List.getElem?_eq_getElem hpos, Option.map_some,
      Option.getD_some]
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos,
      Option.getD_some] at h0
  have hheadB : (bs.head?.map (fun t => t.shape)).getD [] = [rows, cols] := by
    have hpos : 0 < bs.length := by rw [hlenB]; exact hn
    have h0 := hB 0 hn
    rw [List.head?_eq_getElem? , List.getElem?_eq_getElem hpos, Option.map_some,
      Option.getD_some]
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos,
      Option.getD_some] at h0
  have hshA : ∀ k (_ : k < n), (as.getD k (zeroTensor [rows, cols])).shape = [rows, cols] := hA
  have hFshape : ∀ k (_ : k < n),
      (fulls.getD k (zeroTensor [rows * 2, cols])).shape = [rows * 2, cols] := by
    intro k hk
    rw [hF k hk]
    have hh : (([as.getD k (zeroTensor [rows, cols]),
        bs.getD k (zeroTensor [rows, cols])] : List Tensor).head?.map
        (fun t => t.shape)).getD [] = [rows, cols] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      exact hA k hk
    rw [allGatherPrimDimN_shape 0 2 _ _ hh]
    simp [List.set, List.getD]
  have hheadF : (fulls.head?.map (fun t => t.shape)).getD [] = [rows * 2, cols] := by
    have hpos : 0 < fulls.length := by rw [hlenF]; exact hn
    have h0 := hFshape 0 hn
    rw [List.head?_eq_getElem? , List.getElem?_eq_getElem hpos, Option.map_some,
      Option.getD_some]
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos,
      Option.getD_some] at h0
  -- Stack shapes.
  have hLHSshape : (fw_stack fulls).shape = [n, rows * 2, cols] := by
    rw [fw_stack_shape_2d fulls (rows * 2) cols hheadF, hlenF]
  have hSA : (fw_stack as).shape = [n, rows, cols] := by
    rw [fw_stack_shape_2d as rows cols hheadA, hlenA]
  have hSB : (fw_stack bs).shape = [n, rows, cols] := by
    rw [fw_stack_shape_2d bs rows cols hheadB, hlenB]
  have hheadS : (([fw_stack as, fw_stack bs] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [n, rows, cols] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    exact hSA
  have hRHSshape : (allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs]).shape =
      [n, rows * 2, cols] := by
    rw [allGatherPrimDimN_shape 1 2 _ _ hheadS]
    simp [List.set, List.getD]
  refine Tensor.ext (by rw [hLHSshape, hRHSshape]) ?_
  intro idx hidx
  rw [hLHSshape] at hidx
  simp only [prodShape, List.foldl, Nat.one_mul] at hidx
  have hidx' : idx < n * (rows * 2 * cols) := by
    calc idx < n * (rows * 2) * cols := hidx
      _ = n * (rows * 2 * cols) := by ring
  -- Decompose `idx = layer * (rows*2*cols) + (r*rows + i)*cols + k`.
  have hfd : 0 < rows * 2 * cols := by positivity
  have hrc : 0 < rows * cols := Nat.mul_pos hrows hcols
  obtain ⟨layer, loc, hlayerLt, hlocLt, rfl⟩ :
      ∃ layer loc, layer < n ∧ loc < rows * 2 * cols ∧
        idx = layer * (rows * 2 * cols) + loc :=
    ⟨idx / (rows * 2 * cols), idx % (rows * 2 * cols),
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hidx'),
      Nat.mod_lt _ hfd, (Nat.div_add_mod' idx (rows * 2 * cols)).symm⟩
  obtain ⟨jF, k, hjFLt, hkLt, rfl⟩ :
      ∃ jF k, jF < rows * 2 ∧ k < cols ∧ loc = jF * cols + k :=
    ⟨loc / cols, loc % cols,
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hlocLt),
      Nat.mod_lt _ hcols, (Nat.div_add_mod' loc cols).symm⟩
  obtain ⟨r, i, hrLt, hiLt, rfl⟩ :
      ∃ r i, r < 2 ∧ i < rows ∧ jF = r * rows + i :=
    ⟨jF / rows, jF % rows,
      Nat.div_lt_of_lt_mul (by omega),
      Nat.mod_lt _ hrows, (Nat.div_add_mod' jF rows).symm⟩
  -- Left: the stack of fulls, then the dim-0 gather inside the chosen member.
  rw [show layer * (rows * 2 * cols) + ((r * rows + i) * cols + k)
      = layer * (rows * 2 * cols) + ((r * rows + i) * cols + k) from rfl]
  rw [fw_stack_valAt_2d fulls (rows * 2) cols (by positivity) hcols hheadF layer
      (by rw [hlenF]; exact hlayerLt) ((r * rows + i) * cols + k)
      (by
        calc (r * rows + i) * cols + k < (r * rows + i) * cols + cols := by omega
          _ = (r * rows + i + 1) * cols := by ring
          _ ≤ (rows * 2) * cols := Nat.mul_le_mul_right _ (by
              have : r ≤ 1 := by omega
              nlinarith [hrLt, hiLt])
          _ = rows * 2 * cols := by ring)]
  rw [hF layer hlayerLt]
  have hhk : (([as.getD layer (zeroTensor [rows, cols]),
      bs.getD layer (zeroTensor [rows, cols])] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [rows, cols] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    exact hA layer hlayerLt
  have hshk : ∀ r' (_ : r' < 2),
      (([as.getD layer (zeroTensor [rows, cols]),
         bs.getD layer (zeroTensor [rows, cols])] : List Tensor).getD r'
         (zeroTensor [rows, cols])).shape = [rows, cols] := by
    intro r' hr'
    match r', hr' with
    | 0, _ => rw [List.getD_cons_zero]; exact hA layer hlayerLt
    | 1, _ => rw [List.getD_cons_succ, List.getD_cons_zero]; exact hB layer hlayerLt
  rw [allGatherPrimDimN0_valAt 2 rows cols _ (by decide) hrows hcols hhk hshk
    r hrLt i hiLt k hkLt]
  -- Right: the dim-1 gather of the two stacks, then the stack inside rank `r`.
  rw [allGatherPrimDimN1_valAt_3D n rows cols [fw_stack as, fw_stack bs] hn hrows hcols
    hheadS r hrLt layer hlayerLt i hiLt k hkLt]
  match r, hrLt with
  | 0, _ =>
    show valAt (as.getD layer (zeroTensor [rows, cols])) (i * cols + k)
      = valAt (fw_stack as) (layer * (rows * cols) + (i * cols + k))
    rw [fw_stack_valAt_2d as rows cols hrows hcols hheadA layer
        (by rw [hlenA]; exact hlayerLt) (i * cols + k)
        (by
          calc i * cols + k < i * cols + cols := by omega
            _ = (i + 1) * cols := by ring
            _ ≤ rows * cols := Nat.mul_le_mul_right _ (by omega))]
  | 1, _ =>
    show valAt (bs.getD layer (zeroTensor [rows, cols])) (i * cols + k)
      = valAt (fw_stack bs) (layer * (rows * cols) + (i * cols + k))
    rw [fw_stack_valAt_2d bs rows cols hrows hcols hheadB layer
        (by rw [hlenB]; exact hlayerLt) (i * cols + k)
        (by
          calc i * cols + k < i * cols + cols := by omega
            _ = (i + 1) * cols := by ring
            _ ≤ rows * cols := Nat.mul_le_mul_right _ (by omega))]

end

end TrainVerify.Denote
