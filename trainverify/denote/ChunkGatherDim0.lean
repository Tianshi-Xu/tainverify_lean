/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.Denote

/-!
# Chunk / all-gather round trip on dim 0

The repo already has `allGatherPrimDimN_chunkPrimDimN_id_*`, but only for fixed
shapes on dims 1-3. The self-decoder MoE branch splits `[4096, 512]` across two
ranks on dim 0, so it needs the dim-0 case — stated generally in `a`, `b` and
`numParts` rather than pinned to one shape.

`allGatherPrimDimN0_valAt` already covers the gather side generically; this file
adds the chunk side and composes the two.
-/

namespace TrainVerify.Denote

-- Scratch: chunk-side valAt on dim 0. General in a, b, numParts.
set_option maxRecDepth 1000000 in
theorem chunkPrimDimN0_valAt (numParts rank a b : Nat) (x : Tensor)
    (hsh : x.shape = [a, b]) (hnp : 0 < numParts) (hb : 0 < b)
    (hr : rank < numParts)
    (i : Nat) (hi : i < a / numParts) (j : Nat) (hj : j < b) :
    valAt (chunkPrimDimN 0 numParts rank x) (i * b + j) =
      valAt x ((rank * (a / numParts) + i) * b + j) := by
  have hnp' : numParts ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  have hloc : i * b + j < a / numParts * b := by
    have h1 : i + 1 ≤ a / numParts := hi
    have : i * b + b ≤ a / numParts * b := by
      calc i * b + b = (i + 1) * b := by ring
        _ ≤ a / numParts * b := Nat.mul_le_mul_right _ h1
    omega
  have hshard : a / numParts * b ≠ 0 := by omega
  have hchunk_shape : (chunkPrimDimN 0 numParts rank x).shape = [a / numParts, b] := by
    rw [chunkPrimDimN_shape 0 numParts rank _ _ hsh hnp']
    simp [List.set, List.getD]
  have hloc_shape : i * b + j < prodShape (chunkPrimDimN 0 numParts rank x).shape := by
    rw [hchunk_shape]; simp [prodShape]; exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hsh, List.getD, List.getElem?_cons_zero,
    Option.getD_some, List.drop, List.foldl, Nat.one_mul,
    if_neg hnp', if_neg hb', if_neg hshard, Nat.mod_eq_of_lt hr]
  -- The local index sits inside one shard: the leading quotient is 0 and the
  -- remainder is the index itself. Then `(i*b+j)/b = i` and `(i*b+j)%b = j`.
  rw [Nat.div_eq_of_lt hloc, Nat.mod_eq_of_lt hloc, Nat.zero_mul, Nat.zero_add]
  -- Left with `(rank*s + (i*b+j)/b)*b + (i*b+j)%b` vs `(rank*s + i)*b + j`.
  have hdiv : (i * b + j) / b = i := by
    have : i * b + j = b * i + j := by ring
    rw [this, Nat.mul_add_div (show 0 < b by omega), Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (i * b + j) % b = j := by
    have : i * b + j = b * i + j := by ring
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [hdiv, hmod]

-- Splitting on dim 0 and gathering back is the identity.
set_option maxRecDepth 1000000 in
theorem allGatherPrimDimN_chunkPrimDimN_id_dim0_2 (x : Tensor) (a b : Nat)
    (hsh : x.shape = [a, b]) (ha : 0 < a) (hb : 0 < b) (hev : a % 2 = 0) :
    allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x] = x := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 0 2 r x).shape = [a / 2, b] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r _ _ hsh (by omega)]
    simp [List.set, List.getD]
  have hhead : ([chunkPrimDimN 0 2 0 x,
      chunkPrimDimN 0 2 1 x].head?.map (·.shape)).getD [] = [a / 2, b] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  have hgetD : ∀ (r : Nat) (_ : r < 2),
      [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x].getD r (zeroTensor [a / 2, b]) =
        chunkPrimDimN 0 2 r x := by
    intro r hr
    have : r = 0 ∨ r = 1 := by omega
    rcases this with rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  have hWs : ∀ r (_ : r < 2),
      ([chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x].getD r
        (zeroTensor [a / 2, b])).shape = [a / 2, b] := by
    intro r hr; rw [hgetD r hr]; exact hchunk_shape r
  have hgather_shape : (allGatherPrimDimN 0 2 0
      [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x]).shape = [a, b] := by
    rw [allGatherPrimDimN_shape 0 2 _ [a / 2, b] hhead]
    simp [List.set, List.getD]
    omega
  symm
  apply Tensor.ext (by rw [hsh, hgather_shape])
  intro idx hidx
  rw [hsh] at hidx
  have hidxlt : idx < a * b := by simpa [prodShape] using hidx
  set r := idx / (a / 2 * b) with hrdef
  set loc := idx % (a / 2 * b) with hlocdef
  have hab : a / 2 * b * 2 = a * b := by
    have : a / 2 * 2 = a := by omega
    calc a / 2 * b * 2 = a / 2 * 2 * b := by ring
      _ = a * b := by rw [this]
  have hr : r < 2 := by
    rw [hrdef]
    apply Nat.div_lt_of_lt_mul
    omega
  have hloc : loc < a / 2 * b := Nat.mod_lt _ (by
    have : 0 < a / 2 := by omega
    exact Nat.mul_pos this (by omega))
  set i := loc / b with hidef
  set j := loc % b with hjdef
  have hj : j < b := Nat.mod_lt _ (by omega)
  have hi : i < a / 2 := by
    rw [hidef]
    apply Nat.div_lt_of_lt_mul
    calc loc < a / 2 * b := hloc
      _ = b * (a / 2) := by ring
  have hidx_eq : idx = (r * (a / 2) + i) * b + j := by
    -- `Nat.div_add_mod` gives `d * (n / d) + n % d`; our shape wants the
    -- quotient first, so commute.
    have h1 : idx = r * (a / 2 * b) + loc := by
      rw [hrdef, hlocdef, Nat.mul_comm]
      exact (Nat.div_add_mod idx (a / 2 * b)).symm
    have h2 : loc = i * b + j := by
      rw [hidef, hjdef, Nat.mul_comm]
      exact (Nat.div_add_mod loc b).symm
    rw [h1, h2]; ring
  rw [hidx_eq]
  rw [allGatherPrimDimN0_valAt 2 (a / 2) b _ (by omega) (by omega) (by omega)
    hhead hWs r hr i hi j hj]
  rw [hgetD r hr]
  exact (chunkPrimDimN0_valAt 2 r a b x hsh (by omega) (by omega) hr i hi j hj).symm

/-- 1D dim-0 all-gather：输出位置 `r * tokens + i`
    对应 rank `r` 的局部位置 `i`。 -/
private theorem allGatherPrimDimN0_valAt_1d
    (tokens : Nat) (htokens : 0 < tokens)
    (xs : List Tensor)
    (hhead :
      (xs.head?.map (fun t => t.shape)).getD [] = [tokens])
    (hshapes :
      ∀ r (_ : r < 2),
        (xs.getD r (zeroTensor [tokens])).shape = [tokens])
    (r : Nat) (hr : r < 2)
    (i : Nat) (hi : i < tokens) :
    valAt (allGatherPrimDimN 0 2 0 xs) (r * tokens + i) =
      valAt (xs.getD r (zeroTensor [tokens])) i := by
  unfold allGatherPrimDimN
  rw [hhead]
  simp only [List.getD, List.drop, List.foldl]

  have hbound : r * tokens + i < tokens * 2 := by
    calc
      r * tokens + i < r * tokens + tokens := by omega
      _ = (r + 1) * tokens := by ring
      _ ≤ 2 * tokens := Nat.mul_le_mul_right _ (by omega)
      _ = tokens * 2 := by ring

  rw [valAt_of_lt _ _ (by
    show
      r * tokens + i <
        prodShape ([tokens].set 0 (([tokens].getD 0 0) * 2))
    simp [prodShape, List.set, List.getD]
    exact hbound)]

  simp [Tensor.mkShape, List.set, List.getD]

  have htokens_ne : tokens ≠ 0 :=
    Nat.pos_iff_ne_zero.mp htokens

  have hfull_ne : tokens * 2 ≠ 0 :=
    Nat.mul_ne_zero htokens_ne (by omega)

  have hidx_div_full :
      (r * tokens + i) / (tokens * 2) = 0 := by
    exact Nat.div_eq_of_lt hbound

  have hidx_mod_full :
      (r * tokens + i) % (tokens * 2) = r * tokens + i := by
    exact Nat.mod_eq_of_lt hbound

  have hrank :
      (r * tokens + i) / tokens = r := by
    have h :
        (r * tokens + i) / tokens = i / tokens + r := by
      rw [Nat.add_comm, Nat.add_mul_div_right i r htokens]
    rw [h, Nat.div_eq_of_lt hi]
    ring

  have hlocal :
      (r * tokens + i) % tokens = i := by
    have h :
        (r * tokens + i) % tokens = i % tokens := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [h, Nat.mod_eq_of_lt hi]

  have hmod_one :
      (r * tokens + i) % 1 = 0 :=
    Nat.mod_one _

  simp [htokens_ne, hfull_ne, hidx_div_full, hidx_mod_full,
    hrank, hlocal, hmod_one]


/-- 对 shape `[tokens * 2]` 的 1D tensor 在 dim 0 做 chunk：
    rank `r` 的局部位置 `i` 对应原 tensor 的 `r * tokens + i`。 -/
private theorem chunkPrimDimN0_valAt_1d
    (tokens : Nat) (htokens : 0 < tokens)
    (x : Tensor)
    (hshape : x.shape = [tokens * 2])
    (r : Nat) (hr : r < 2)
    (i : Nat) (hi : i < tokens) :
    valAt (chunkPrimDimN 0 2 r x) i =
      valAt x (r * tokens + i) := by
  unfold chunkPrimDimN
  rw [hshape]
  simp only [List.set, List.drop, List.foldl, List.getD]

  have hdiv : (tokens * 2) / 2 = tokens := by
    omega

  have hrmod : r % 2 = r :=
    Nat.mod_eq_of_lt hr

  rw [valAt_of_lt _ _ (by
    show
      i <
        prodShape ([tokens * 2].set 0 ((tokens * 2) / 2))
    simp [prodShape, List.set, hdiv]
    exact hi)]

  simp [Tensor.mkShape, List.set, hdiv, hrmod]

  have himod : i % tokens = i :=
    Nat.mod_eq_of_lt hi

  have hidiv : i / tokens = 0 :=
    Nat.div_eq_of_lt hi

  have htokens_ne : tokens ≠ 0 :=
    Nat.pos_iff_ne_zero.mp htokens

  have himod_one : i % 1 = 0 :=
    Nat.mod_one _

  simp [himod, hidiv, htokens_ne, himod_one]


/- 一个 shape 为 `[2 * tokens]` 的 1D tensor，在 dim 0 上分成两个 rank，
   再按 dim 0 all-gather 后恢复原 tensor。 -/
set_option maxRecDepth 1000000 in
theorem allGatherPrimDimN_chunkPrimDimN_id_dim0_2_1d
    (x : Tensor) (tokens : Nat)
    (hshape : x.shape = [2 * tokens])
    (htokens : 0 < tokens) :
    allGatherPrimDimN 0 2 0
      [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x] = x := by
  have hshape' : x.shape = [tokens * 2] := by
    simpa [Nat.mul_comm] using hshape

  have hchunk_shape :
      ∀ r, (chunkPrimDimN 0 2 r x).shape = [tokens] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r x [tokens * 2] hshape' (by omega)]
    simp [List.set, List.getD]

  have hhead :
      ([chunkPrimDimN 0 2 0 x,
          chunkPrimDimN 0 2 1 x].head?.map (fun t => t.shape)).getD [] =
        [tokens] := by
    simp [List.head?, Option.map, hchunk_shape 0]

  have hgetD :
      ∀ r (_ : r < 2),
        [chunkPrimDimN 0 2 0 x,
          chunkPrimDimN 0 2 1 x].getD r (zeroTensor [tokens]) =
            chunkPrimDimN 0 2 r x := by
    intro r hr
    have hr_cases : r = 0 ∨ r = 1 := by
      omega
    rcases hr_cases with rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ]

  have hshapes :
      ∀ r (_ : r < 2),
        ([chunkPrimDimN 0 2 0 x,
            chunkPrimDimN 0 2 1 x].getD r
              (zeroTensor [tokens])).shape = [tokens] := by
    intro r hr
    rw [hgetD r hr]
    exact hchunk_shape r

  have hgather_shape :
      (allGatherPrimDimN 0 2 0
        [chunkPrimDimN 0 2 0 x,
          chunkPrimDimN 0 2 1 x]).shape = [tokens * 2] := by
    rw [allGatherPrimDimN_shape 0 2 _ [tokens] hhead]
    simp [List.set, List.getD]

  symm
  apply Tensor.ext (by rw [hshape', hgather_shape])
  intro idx hidx

  rw [hshape'] at hidx

  have hidxlt : idx < tokens * 2 := by
    simpa [prodShape] using hidx

  set r := idx / tokens with hrdef
  set i := idx % tokens with hidef

  have hr : r < 2 := by
    rw [hrdef]
    apply Nat.div_lt_of_lt_mul
    exact hidxlt

  have hi : i < tokens := by
    rw [hidef]
    exact Nat.mod_lt idx (by omega)

  have hidx_eq : idx = r * tokens + i := by
    rw [hrdef, hidef, Nat.mul_comm]
    exact (Nat.div_add_mod idx tokens).symm

  rw [hidx_eq]

  rw [allGatherPrimDimN0_valAt_1d
    tokens htokens
    [chunkPrimDimN 0 2 0 x, chunkPrimDimN 0 2 1 x]
    hhead hshapes r hr i hi]

  rw [hgetD r hr]

  exact
    (chunkPrimDimN0_valAt_1d
      tokens htokens x hshape' r hr i hi).symm

end TrainVerify.Denote
