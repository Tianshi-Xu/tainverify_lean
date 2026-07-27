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

end TrainVerify.Denote
