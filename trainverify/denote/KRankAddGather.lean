import denote.Denote

open TrainVerify.Denote

namespace TrainVerify.Denote

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

private theorem kr_prodShape_cons (d : Nat) (rest : Shape) :
    prodShape (d :: rest) = d * prodShape rest := by
  simp only [prodShape, List.foldl]
  suffices ∀ (a : Nat) (bs : List Nat), List.foldl (fun acc d => acc * d) a bs =
      a * List.foldl (fun acc d => acc * d) 1 bs by rw [this]; simp
  intro a bs
  induction bs generalizing a with
  | nil => simp [List.foldl]
  | cons b bs ih =>
      simp only [List.foldl, Nat.one_mul]
      rw [ih, ih b]
      exact Nat.mul_assoc a b _

private theorem kr_flatToMulti_length (sh : Shape) (k : Nat) :
    (flatToMulti sh k).length = sh.length := by
  induction sh generalizing k with
  | nil => rfl
  | cons d rest ih =>
      change (let stride := prodShape rest
        if stride = 0 then 0 :: flatToMulti rest 0
        else (k / stride) :: flatToMulti rest (k % stride)).length = _
      dsimp only []
      split_ifs
      · simp only [List.length_cons]; exact congrArg Nat.succ (ih 0)
      · simp only [List.length_cons]; exact congrArg Nat.succ (ih _)

private theorem kr_flatToMulti_zero_at_one (sh : Shape) (k i : Nat)
    (hk : k < prodShape sh) (hi : i < sh.length) (hdim : sh[i] = 1) :
    (flatToMulti sh k)[i]'(by rw [kr_flatToMulti_length]; exact hi) = 0 := by
  induction sh generalizing k i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons d rest ih =>
      have hne : prodShape rest ≠ 0 := by
        intro h
        rw [kr_prodShape_cons] at hk
        simp [h] at hk
      have hpos : 0 < prodShape rest := Nat.pos_of_ne_zero hne
      have hfm : flatToMulti (d :: rest) k =
          (k / prodShape rest) :: flatToMulti rest (k % prodShape rest) := by
        change (let stride := prodShape rest
          if stride = 0 then 0 :: flatToMulti rest 0
          else (k / stride) :: flatToMulti rest (k % stride)) = _
        dsimp only []
        rw [if_neg hne]
      match i, hi, hdim with
      | 0, _, hdim0 =>
          have hd : d = 1 := hdim0
          subst hd
          rw [kr_prodShape_cons, Nat.one_mul] at hk
          simp [hfm, Nat.div_eq_of_lt hk]
      | i' + 1, hi_succ, hdim_succ =>
          have hi_rest : i' < rest.length := by
            have : (d :: rest).length = rest.length + 1 := rfl
            omega
          have key : (flatToMulti (d :: rest) k)[i' + 1]'(by
              rw [kr_flatToMulti_length]; exact hi_succ) =
              (flatToMulti rest (k % prodShape rest))[i']'(by
                rw [kr_flatToMulti_length]; exact hi_rest) := by
            simp only [hfm, List.getElem_cons_succ]
          rw [key]
          exact ih (k % prodShape rest) i' (Nat.mod_lt k hpos) hi_rest hdim_succ

private theorem kr_multiToFlat_flatToMulti (sh : Shape) (k : Nat)
    (hk : k < prodShape sh) : multiToFlat sh (flatToMulti sh k) = k := by
  induction sh generalizing k with
  | nil =>
      have hk0 : k = 0 := by
        have : prodShape ([] : List Nat) = 1 := rfl
        omega
      subst hk0
      rfl
  | cons d rest ih =>
      have hne : prodShape rest ≠ 0 := by
        intro h
        rw [kr_prodShape_cons] at hk
        simp [h] at hk
      have hpos : 0 < prodShape rest := Nat.pos_of_ne_zero hne
      have hfm : flatToMulti (d :: rest) k =
          (k / prodShape rest) :: flatToMulti rest (k % prodShape rest) := by
        change (let stride := prodShape rest
          if stride = 0 then 0 :: flatToMulti rest 0
          else (k / stride) :: flatToMulti rest (k % stride)) = _
        dsimp only []
        rw [if_neg hne]
      rw [hfm]
      show k / prodShape rest * prodShape rest +
          multiToFlat rest (flatToMulti rest (k % prodShape rest)) = k
      rw [ih _ (Nat.mod_lt k hpos), Nat.mul_comm]
      exact Nat.div_add_mod k (prodShape rest)

private theorem kr_multiToFlat_aligned_same (sh : Shape) (k : Nat)
    (hk : k < prodShape sh) : multiToFlat sh (alignedMultiIndex sh sh k) = k := by
  suffices h : alignedMultiIndex sh sh k = flatToMulti sh k by
    rw [h]
    exact kr_multiToFlat_flatToMulti sh k hk
  simp only [alignedMultiIndex, Nat.sub_self, List.drop_zero]
  apply List.ext_getElem (by simp [kr_flatToMulti_length])
  intro i hi1 hi2
  simp only [List.getElem_ofFn]
  have hi_sh : i < sh.length := by
    have := kr_flatToMulti_length sh k
    omega
  split_ifs with hdim
  · have hdim' : sh[i] = 1 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_sh] at hdim
      exact hdim
    have h0 := kr_flatToMulti_zero_at_one sh k i hk hi_sh hdim'
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
    simp

private theorem kr_broadcast_self (t : Tensor) (sh : Shape) (idx : Nat)
    (ht : t.shape = sh) (hidx : idx < prodShape sh) :
    broadcastValAtShape sh t idx = valAt t idx := by
  unfold broadcastValAtShape
  rw [ht, kr_multiToFlat_aligned_same sh idx hidx]

/-- Elementwise addition reads equal-shaped 3-D tensors pointwise. -/
theorem elemwiseAdd_valAt_3d
    (x y : Tensor) (b s d idx : Nat)
    (hx : x.shape = [b, s, d]) (hy : y.shape = [b, s, d])
    (hidx : idx < b * s * d) :
    valAt (elemwiseAdd x y) idx = valAt x idx + valAt y idx := by
  have hout : (elemwiseAdd x y).shape = [b, s, d] :=
    elemwiseAdd_shape_of_shapes x y [b, s, d] hx hy
  have hprod : prodShape [b, s, d] = b * s * d := by simp [prodShape]
  have hidx' : idx < prodShape [b, s, d] := by rwa [hprod]
  have hos : outShape2 x y = [b, s, d] := by simp [outShape2, hx, hy]
  have hstep : valAt (elemwiseAdd x y) idx =
      broadcastValAtShape (outShape2 x y) x idx +
        broadcastValAtShape (outShape2 x y) y idx := by
    rw [valAt_of_lt _ _ (by rw [hout]; exact hidx')]
    rfl
  rw [hstep, hos, kr_broadcast_self x [b, s, d] idx hx hidx',
    kr_broadcast_self y [b, s, d] idx hy hidx']

private theorem list_getD_of_lt {α : Type*} (l : List α) (i : Nat) (d : α)
    (h : i < l.length) : l.getD i d = l[i] := by
  unfold List.getD
  rw [List.getElem?_eq_getElem h]
  rfl

private theorem list_getD_of_ge {α : Type*} (l : List α) (i : Nat) (d : α)
    (h : ¬ i < l.length) : l.getD i d = d := by
  unfold List.getD
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-- For arbitrary positive `K` and arbitrary positive 3-D shard shape `[B,S,D]`,
pointwise addition commutes with dimension-1 all-gather.  `zipWith` preserves the
ordered pairing of the two equal-length shard lists. -/
theorem fw_add_allGather_dim1_K
    (K B S D : Nat) (xs ys : List Tensor)
    (hK : 0 < K) (hB : 0 < B) (hS : 0 < S) (hD : 0 < D)
    (hxs_len : xs.length = K) (hys_len : ys.length = K)
    (hxy_len : xs.length = ys.length)
    (hxs_shape : ∀ r (hr : r < xs.length), (xs.get ⟨r, hr⟩).shape = [B, S, D])
    (hys_shape : ∀ r (hr : r < ys.length), (ys.get ⟨r, hr⟩).shape = [B, S, D]) :
    elemwiseAdd (allGatherPrimDimN 1 K 0 xs) (allGatherPrimDimN 1 K 0 ys) =
      allGatherPrimDimN 1 K 0 (List.zipWith elemwiseAdd xs ys) := by
  have hhead_xs : (xs.head?.map (fun t => t.shape)).getD [] = [B, S, D] := by
    have h0 : 0 < xs.length := by omega
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
    simp only [Option.map_some, Option.getD_some]
    exact hxs_shape 0 h0
  have hhead_ys : (ys.head?.map (fun t => t.shape)).getD [] = [B, S, D] := by
    have h0 : 0 < ys.length := by omega
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
    simp only [Option.map_some, Option.getD_some]
    exact hys_shape 0 h0
  have hzip_len : (List.zipWith elemwiseAdd xs ys).length = K := by
    rw [List.length_zipWith, hxs_len, hys_len, Nat.min_self]
  have hhead_zip :
      ((List.zipWith elemwiseAdd xs ys).head?.map (fun t => t.shape)).getD [] =
        [B, S, D] := by
    have h0z : 0 < (List.zipWith elemwiseAdd xs ys).length := by omega
    have h0x : 0 < xs.length := by omega
    have h0y : 0 < ys.length := by omega
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0z]
    simp only [Option.map_some, Option.getD_some]
    have hz0 : (List.zipWith elemwiseAdd xs ys)[0]'h0z =
        elemwiseAdd (xs[0]'h0x) (ys[0]'h0y) := List.getElem_zipWith
    rw [hz0]
    exact elemwiseAdd_shape_of_shapes _ _ _ (hxs_shape 0 h0x) (hys_shape 0 h0y)
  have hshape_x : (allGatherPrimDimN 1 K 0 xs).shape = [B, S * K, D] := by
    rw [allGatherPrimDimN_shape 1 K xs [B, S, D] hhead_xs]
    rfl
  have hshape_y : (allGatherPrimDimN 1 K 0 ys).shape = [B, S * K, D] := by
    rw [allGatherPrimDimN_shape 1 K ys [B, S, D] hhead_ys]
    rfl
  have hshape_zip :
      (allGatherPrimDimN 1 K 0 (List.zipWith elemwiseAdd xs ys)).shape =
        [B, S * K, D] := by
    rw [allGatherPrimDimN_shape 1 K _ [B, S, D] hhead_zip]
    rfl
  have hshape_add :
      (elemwiseAdd (allGatherPrimDimN 1 K 0 xs)
        (allGatherPrimDimN 1 K 0 ys)).shape = [B, S * K, D] :=
    elemwiseAdd_shape_of_shapes _ _ _ hshape_x hshape_y
  apply Tensor.ext
  · rw [hshape_add, hshape_zip]
  · intro idx hidx
    have hidx_out : idx < B * (S * K) * D := by
      rw [hshape_add] at hidx
      simpa [prodShape, Nat.mul_assoc] using hidx
    rw [elemwiseAdd_valAt_3d _ _ B (S * K) D idx hshape_x hshape_y hidx_out]
    have hxlt : idx < prodShape (allGatherPrimDimN 1 K 0 xs).shape := by
      rw [hshape_x]
      simpa [prodShape, Nat.mul_assoc] using hidx_out
    have hylt : idx < prodShape (allGatherPrimDimN 1 K 0 ys).shape := by
      rw [hshape_y]
      simpa [prodShape, Nat.mul_assoc] using hidx_out
    have hzlt : idx < prodShape
        (allGatherPrimDimN 1 K 0 (List.zipWith elemwiseAdd xs ys)).shape := by
      rw [hshape_zip]
      simpa [prodShape, Nat.mul_assoc] using hidx_out
    rw [valAt_of_lt _ _ hxlt, valAt_of_lt _ _ hylt, valAt_of_lt _ _ hzlt]
    simp only [allGatherPrimDimN, Tensor.mkShape, hhead_xs, hhead_ys, hhead_zip]
    set ds := List.getD [B, S, D] 1 0
    set ps := List.foldl (· * ·) 1 (List.drop (1 + 1) [B, S, D])
    set fds := ds * K * ps
    generalize hr_def : (if ds = 0 then 0
      else (if ps = 0 then 0
        else (if fds = 0 then 0 else idx % fds) / ps) / ds) = r
    generalize hloc_def : (if fds = 0 then 0 else idx / fds) * (ds * ps) +
      (if ds = 0 then 0
        else (if ps = 0 then 0
          else (if fds = 0 then 0 else idx % fds) / ps) % ds) * ps +
      (if ps = 0 then 0 else (if fds = 0 then 0 else idx % fds) % ps) = loc
    by_cases hrK : r < K
    · have hrx : r < xs.length := by omega
      have hry : r < ys.length := by omega
      have hrz : r < (List.zipWith elemwiseAdd xs ys).length := by omega
      rw [list_getD_of_lt _ _ _ hrx, list_getD_of_lt _ _ _ hry,
        list_getD_of_lt _ _ _ hrz]
      have hzelem : (List.zipWith elemwiseAdd xs ys)[r]'hrz =
          elemwiseAdd (xs[r]'hrx) (ys[r]'hry) := List.getElem_zipWith
      rw [hzelem]
      have hxsh := hxs_shape r hrx
      have hysh := hys_shape r hry
      by_cases hloc : loc < prodShape [B, S, D]
      · have hloc' : loc < B * S * D := by
          simpa [prodShape, Nat.mul_assoc] using hloc
        exact (elemwiseAdd_valAt_3d _ _ B S D loc hxsh hysh hloc').symm
      · have hzsh := elemwiseAdd_shape_of_shapes (xs[r]'hrx) (ys[r]'hry)
          [B, S, D] hxsh hysh
        have hnx : ¬ loc < prodShape (xs[r]'hrx).shape := by
          rw [show (xs[r]'hrx).shape = [B, S, D] from hxs_shape r hrx]
          exact hloc
        have hny : ¬ loc < prodShape (ys[r]'hry).shape := by
          rw [show (ys[r]'hry).shape = [B, S, D] from hys_shape r hry]
          exact hloc
        have hnz : ¬ loc < prodShape (elemwiseAdd (xs[r]'hrx) (ys[r]'hry)).shape := by
          rw [hzsh]; exact hloc
        simp [valAt, hnx, hny, hnz]
    · have hrx : ¬ r < xs.length := by omega
      have hry : ¬ r < ys.length := by omega
      have hrz : ¬ r < (List.zipWith elemwiseAdd xs ys).length := by omega
      rw [list_getD_of_ge _ _ _ hrx, list_getD_of_ge _ _ _ hry,
        list_getD_of_ge _ _ _ hrz]
      simp [zeroTensor, Tensor.mkShape, valAt, prodShape]


end TrainVerify.Denote
