/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.Denote

/-!
# Value-faithful zigzag context-parallel collectives

This module refines Denote's intentionally local `fw_maybe_shuffle` /
`fw_maybe_unshuffle` identity abstraction with semantics that can observe every rank's
input shard.  It is a standalone collective model and is not wired into `evalOp`.

The pinned authority is NNScaler 0.9, commit `1102e629`, in particular
[`_compute_a2a_metadata`](https://github.com/microsoft/nnscaler/blob/1102e629/nnscaler/customized_ops/ring_attention/varlen_utils.py#L79-L165),
[`shuffle_varlen`](https://github.com/microsoft/nnscaler/blob/1102e629/nnscaler/customized_ops/ring_attention/varlen_utils.py#L172-L189), and
[`unshuffle_varlen`](https://github.com/microsoft/nnscaler/blob/1102e629/nnscaler/customized_ops/ring_attention/varlen_utils.py#L192-L209).
The index arithmetic is shared with the retained, documented helpers in
`denote.Denote`: `zigzagPos`, `destRank`, `zigzagInvOffset`, and `gatherFromRank`.
-/

open TrainVerify.Denote

namespace TrainVerify.Denote.ZigzagCollective
noncomputable section

/-- Well-formed packed cumulative sequence metadata and a complete set of uniformly
shaped local shards.  In addition to positive/rank-complete CP, boundaries start at
zero, are monotone, every sequence admits the authority's `2 * cpSize` slicing, and
the local token dimensions reconstruct the final cumulative endpoint. -/
structure ZigzagCuWF (cu : List Nat) (xs : List Tensor) (cpSize : Nat) : Prop where
  cp_pos : 0 < cpSize
  ranks : xs.length = cpSize
  cu_starts_zero : cu.head?.getD 0 = 0
  cu_has_endpoint : 2 ≤ cu.length
  monotone : ∀ s, s + 1 < cu.length → cu.getD s 0 ≤ cu.getD (s + 1) 0
  divisible : ∀ s, s + 1 < cu.length →
    (cu.getD (s + 1) 0 - cu.getD s 0) % (2 * cpSize) = 0
  shapes_nonempty : ∀ x ∈ xs, x.shape ≠ []
  same_shape : ∀ x ∈ xs, x.shape = (xs.getD 0 (zeroTensor [])).shape
  local_tokens :
    (xs.getD 0 (zeroTensor [])).shape.getD 0 0 * cpSize = listLast! cu

/-- Convert ordinary contiguous rank shards to NNScaler's zigzag layout.

At `cpSize = 1` this follows NNScaler's collective-free identity behavior exactly.
Otherwise output token `k` gathers global position `zigzagPos cu cpSize cpRank k`
from the corresponding ordinary source shard. -/
noncomputable def fw_maybe_shuffle_collective
    (xs : List Tensor) (cu : List Nat) (cpSize cpRank : Nat) : Tensor :=
  let localTensor := xs.getD cpRank (zeroTensor [])
  if cpSize = 1 then localTensor
  else
    let chunk := localTensor.shape.getD 0 0
    let hiddenStride := prodShape localTensor.shape.tail
    Tensor.mkShape localTensor.shape (fun i =>
      let token := i.val / hiddenStride
      let h := i.val % hiddenStride
      gatherFromRank xs chunk hiddenStride (zigzagPos cu cpSize cpRank token) h)

/-- Convert NNScaler zigzag rank shards back to ordinary contiguous rank shards.
For each ordinary global position, `destRank` and `zigzagInvOffset` locate its source
in the zigzag collective. -/
noncomputable def fw_maybe_unshuffle_collective
    (xs : List Tensor) (cu : List Nat) (cpSize cpRank : Nat) : Tensor :=
  let localTensor := xs.getD cpRank (zeroTensor [])
  if cpSize = 1 then localTensor
  else
    let chunk := localTensor.shape.getD 0 0
    let hiddenStride := prodShape localTensor.shape.tail
    Tensor.mkShape localTensor.shape (fun i =>
      let token := i.val / hiddenStride
      let h := i.val % hiddenStride
      let globalPos := cpRank * chunk + token
      let srcRank := destRank cu cpSize globalPos
      let srcOffset := zigzagInvOffset cu cpSize srcRank globalPos
      valAt (xs.getD srcRank (zeroTensor [])) (srcOffset * hiddenStride + h))

@[simp] theorem fw_maybe_shuffle_collective_shape
    (xs : List Tensor) (cu : List Nat) (cpSize cpRank : Nat) :
    (fw_maybe_shuffle_collective xs cu cpSize cpRank).shape =
      (xs.getD cpRank (zeroTensor [])).shape := by
  by_cases hcp : cpSize = 1
  · simp [fw_maybe_shuffle_collective, hcp]
  · simp [fw_maybe_shuffle_collective, hcp, Tensor.mkShape]

@[simp] theorem fw_maybe_unshuffle_collective_shape
    (xs : List Tensor) (cu : List Nat) (cpSize cpRank : Nat) :
    (fw_maybe_unshuffle_collective xs cu cpSize cpRank).shape =
      (xs.getD cpRank (zeroTensor [])).shape := by
  by_cases hcp : cpSize = 1
  · simp [fw_maybe_unshuffle_collective, hcp]
  · simp [fw_maybe_unshuffle_collective, hcp, Tensor.mkShape]

/-- On the sole valid rank, the faithful shuffle is extensionally the input Tensor. -/
@[simp] theorem fw_maybe_shuffle_collective_cpSize_one
    (xs : List Tensor) (cu : List Nat) (cpRank : Nat) (_hrank : cpRank = 0) :
    fw_maybe_shuffle_collective xs cu 1 cpRank = xs.getD cpRank (zeroTensor []) := by
  simp [fw_maybe_shuffle_collective]

/-- On the sole valid rank, the faithful unshuffle is extensionally the input Tensor. -/
@[simp] theorem fw_maybe_unshuffle_collective_cpSize_one
    (xs : List Tensor) (cu : List Nat) (cpRank : Nat) (_hrank : cpRank = 0) :
    fw_maybe_unshuffle_collective xs cu 1 cpRank = xs.getD cpRank (zeroTensor []) := by
  simp [fw_maybe_unshuffle_collective]

/-- In-bounds value behavior of the nontrivial shuffle branch. -/
theorem fw_maybe_shuffle_collective_valAt
    (xs : List Tensor) (cu : List Nat) (cpSize cpRank i : Nat)
    (hcp : cpSize ≠ 1)
    (hi : i < prodShape (xs.getD cpRank (zeroTensor [])).shape) :
    valAt (fw_maybe_shuffle_collective xs cu cpSize cpRank) i =
      let localTensor := xs.getD cpRank (zeroTensor [])
      let hiddenStride := prodShape localTensor.shape.tail
      let token := i / hiddenStride
      let h := i % hiddenStride
      gatherFromRank xs (localTensor.shape.getD 0 0) hiddenStride
        (zigzagPos cu cpSize cpRank token) h := by
  unfold fw_maybe_shuffle_collective
  simp only [hcp, ↓reduceIte]
  conv_lhs =>
    rw [valAt_of_lt _ _ (by simpa [Tensor.mkShape] using hi)]
  rfl

/-- In-bounds value behavior of the nontrivial inverse branch. -/
theorem fw_maybe_unshuffle_collective_valAt
    (xs : List Tensor) (cu : List Nat) (cpSize cpRank i : Nat)
    (hcp : cpSize ≠ 1)
    (hi : i < prodShape (xs.getD cpRank (zeroTensor [])).shape) :
    valAt (fw_maybe_unshuffle_collective xs cu cpSize cpRank) i =
      let localTensor := xs.getD cpRank (zeroTensor [])
      let chunk := localTensor.shape.getD 0 0
      let hiddenStride := prodShape localTensor.shape.tail
      let token := i / hiddenStride
      let h := i % hiddenStride
      let globalPos := cpRank * chunk + token
      let srcRank := destRank cu cpSize globalPos
      let srcOffset := zigzagInvOffset cu cpSize srcRank globalPos
      valAt (xs.getD srcRank (zeroTensor [])) (srcOffset * hiddenStride + h) := by
  unfold fw_maybe_unshuffle_collective
  simp only [hcp, ↓reduceIte]
  conv_lhs =>
    rw [valAt_of_lt _ _ (by simpa [Tensor.mkShape] using hi)]
  rfl

/-- Every lookup in the empty-shaped zero tensor is zero. -/
@[simp] theorem valAt_zeroTensor_empty (i : Nat) :
    valAt (zeroTensor []) i = 0 := by
  unfold valAt zeroTensor Tensor.mkShape
  simp [prodShape]

/-- Lightweight core form of the dim-0 RMSNorm/all-gather commute theorem.
Row-wise reduction is orthogonal to dim-0 sharding. -/
theorem fw_rms_norm_allGather0_commute_2_core
    (a b w : Tensor) (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (ha : a.shape = [shard, hidden]) (hb : b.shape = [shard, hidden]) :
    fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w
      = allGatherPrimDimN 0 2 0 [fw_rms_norm a w, fw_rms_norm b w] := by
  have hhead : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by simp [ha]
  have hG_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead]; simp [List.set, List.getD]
  have hrms_shape : ∀ c : Tensor, c.shape = [shard, hidden] → (fw_rms_norm c w).shape = [shard, hidden] := by
    intro c hc; unfold fw_rms_norm; rw [hc]; simp [Tensor.mkShape]
  have hrms_a : (fw_rms_norm a w).shape = [shard, hidden] := hrms_shape a ha
  have hrms_b : (fw_rms_norm b w).shape = [shard, hidden] := hrms_shape b hb
  have hhead_rms : (([fw_rms_norm a w, fw_rms_norm b w] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [hrms_a]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [fw_rms_norm a w, fw_rms_norm b w]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_rms]; simp [List.set, List.getD]
  have hLHS_shape : (fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w).shape = [shard * 2, hidden] := by
    unfold fw_rms_norm; rw [hG_shape]; simp [Tensor.mkShape]
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < shard * 2 * hidden := by simpa [prodShape] using hidx
    set row := idx / hidden with hrow_def
    set j := idx % hidden with hj_def
    have hj_lt : j < hidden := by rw [hj_def]; exact Nat.mod_lt _ hhid
    have hrow_lt : row < 2 * shard := by
      rw [hrow_def]; exact Nat.div_lt_iff_lt_mul hhid |>.mpr (by linarith [hidx_bound])
    set r := row / shard with hr_def
    set i := row % shard with hi_def
    have hi_lt : i < shard := by rw [hi_def]; exact Nat.mod_lt _ hshard
    have hr_lt : r < 2 := by
      rw [hr_def]; exact Nat.div_lt_iff_lt_mul hshard |>.mpr (by linarith [hrow_lt])
    have hidx_eq : idx = (r * shard + i) * hidden + j := by
      rw [hr_def, hi_def, hj_def, hrow_def]
      have h1 : row = shard * (row / shard) + row % shard := (Nat.div_add_mod row shard).symm
      have h2 : idx = hidden * (idx / hidden) + idx % hidden := (Nat.div_add_mod idx hidden).symm
      calc idx = hidden * (idx / hidden) + idx % hidden := h2
        _ = row * hidden + j := by rw [← hrow_def, ← hj_def]; ring
        _ = (shard * (row / shard) + row % shard) * hidden + j := by rw [← h1]
        _ = (row / shard * shard + row % shard) * hidden + j := by ring
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hshapes_rms : ∀ r' (_ : r' < 2),
        (([fw_rms_norm a w, fw_rms_norm b w].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hrms_a, hrms_b]
    have hLHS_val : valAt (fw_rms_norm (allGatherPrimDimN 0 2 0 [a, b]) w) idx =
        (valAt (allGatherPrimDimN 0 2 0 [a, b]) idx *
          (1 / sqrtFn (rmsMeanSqAt (allGatherPrimDimN 0 2 0 [a, b]) (idx / hidden) hidden + rmsNormEps))) *
          valAt w (idx % hidden) := by
      unfold fw_rms_norm
      rw [show (allGatherPrimDimN 0 2 0 [a, b]).shape.reverse = hidden :: [shard * 2] from by rw [hG_shape]; rfl]
      simp only [Tensor.mkShape, valAt]
      have hidx_lt_prod : idx < prodShape (allGatherPrimDimN 0 2 0 [a, b]).shape := by
        rw [hG_shape]; simp [prodShape]; exact hidx_bound
      simp [hidx_lt_prod]
    rw [hLHS_val, hidx_eq]
    have hrms_commute : rmsMeanSqAt (allGatherPrimDimN 0 2 0 [a, b]) (r * shard + i) hidden =
        rmsMeanSqAt ([a, b].getD r (zeroTensor [shard, hidden])) i hidden := by
      unfold rmsMeanSqAt
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b] (by omega) hshard hhid hhead hshapes_ab r hr_lt i hi_lt k hk]
    have hrow_div : (r * shard + i) * hidden / hidden = r * shard + i := by
      rw [Nat.mul_div_cancel _ hhid]
    have hrow_div' : ((r * shard + i) * hidden + j) / hidden = r * shard + i := by
      rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
          Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
    have hrow_mod : ((r * shard + i) * hidden + j) % hidden = j := by
      rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
    rw [hrow_div', hrow_mod]
    rw [hrms_commute]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b] (by omega) hshard hhid hhead hshapes_ab
          r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [fw_rms_norm a w, fw_rms_norm b w]
          (by omega) hshard hhid hhead_rms hshapes_rms r hr_lt i hi_lt j hj_lt]
    have hr_lt' : r = 0 ∨ r = 1 := by
      interval_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hgetD_rms : [fw_rms_norm a w, fw_rms_norm b w].getD r (zeroTensor [shard, hidden]) =
        fw_rms_norm ([a, b].getD r (zeroTensor [shard, hidden])) w := by
      rcases hr_lt' with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_rms]
    set c := [a, b].getD r (zeroTensor [shard, hidden]) with hc_def
    have hc_shape : c.shape = [shard, hidden] := hshapes_ab r hr_lt
    have hloc_bound : i * hidden + j < shard * hidden := by
      have h1 : i * hidden + j < i * hidden + hidden := by omega
      have h2 : i * hidden + hidden = (i + 1) * hidden := by ring
      have h3 : (i + 1) * hidden ≤ shard * hidden := Nat.mul_le_mul_right _ (by omega)
      omega
    have h_ihidden_div : (i * hidden + j) / hidden = i := by
      rw [show i * hidden + j = j + hidden * i from by ring,
          Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
    have h_ihidden_mod : (i * hidden + j) % hidden = j := by
      rw [show i * hidden + j = j + hidden * i from by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
    unfold fw_rms_norm
    rw [show c.shape.reverse = hidden :: [shard] from by rw [hc_shape]; rfl]
    simp only [Tensor.mkShape, valAt]
    have hloc_lt_prod : i * hidden + j < prodShape c.shape := by
      rw [hc_shape]; simp [prodShape]; exact hloc_bound
    simp [hloc_lt_prod, h_ihidden_div, h_ihidden_mod]

/-- RMSNorm preserves an exact two-dimensional shape. -/
theorem fw_rms_norm_shape_2d (x w : Tensor) (rows hidden : Nat)
    (hx : x.shape = [rows, hidden]) :
    (fw_rms_norm x w).shape = [rows, hidden] := by
  unfold fw_rms_norm
  rw [hx]
  simp [Tensor.mkShape]

/-- In-bounds value formula for two-dimensional RMSNorm. -/
theorem fw_rms_norm_valAt_2d (x w : Tensor) (rows hidden i : Nat)
    (hx : x.shape = [rows, hidden])
    (hi : i < rows * hidden) :
    valAt (fw_rms_norm x w) i =
      (valAt x i *
        (1 / sqrtFn (rmsMeanSqAt x (i / hidden) hidden + rmsNormEps))) *
        valAt w (i % hidden) := by
  unfold fw_rms_norm
  rw [show x.shape.reverse = hidden :: [rows] by rw [hx]; simp]
  simp only [Tensor.mkShape, valAt]
  have hip : i < prodShape x.shape := by
    rw [hx]
    simpa [prodShape] using hi
  simp [hip]

/-- Applying RMSNorm to both CP2 source shards preserves packed-sequence
well-formedness, because the contract depends only on metadata and shard shapes. -/
theorem ZigzagCuWF.rms_norm_cp2
    (cu : List Nat) (source0 source1 w : Tensor) (lDim hidden : Nat)
    (hwf : ZigzagCuWF cu [source0, source1] 2)
    (hs0 : source0.shape = [lDim, hidden])
    (hs1 : source1.shape = [lDim, hidden]) :
    ZigzagCuWF cu [fw_rms_norm source0 w, fw_rms_norm source1 w] 2 := by
  have hrs0 := fw_rms_norm_shape_2d source0 w lDim hidden hs0
  have hrs1 := fw_rms_norm_shape_2d source1 w lDim hidden hs1
  refine ⟨hwf.cp_pos, rfl, hwf.cu_starts_zero, hwf.cu_has_endpoint,
    hwf.monotone, hwf.divisible, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hrs0]
      simp
    · rw [hrs1]
      simp
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp only [List.getD_cons_zero]
    · simp only [List.getD_cons_zero]
      rw [hrs1, hrs0]
  · simpa only [List.getD_cons_zero, hrs0, hs0] using hwf.local_tokens

/-- A faithful CP2 shuffle commutes with row-local RMSNorm.  The shuffle only
permutes complete rows, so every row reduction and the hidden-axis weight lookup
are unchanged. -/
theorem fw_rms_norm_shuffle_collective_cp2
    (source0 source1 w : Tensor) (cu : List Nat) (lDim hidden rank : Nat)
    (hl : 0 < lDim) (hh : 0 < hidden) (hrank : rank < 2)
    (hs0 : source0.shape = [lDim, hidden])
    (hs1 : source1.shape = [lDim, hidden]) :
    fw_rms_norm
        (fw_maybe_shuffle_collective [source0, source1] cu 2 rank) w =
      fw_maybe_shuffle_collective
        [fw_rms_norm source0 w, fw_rms_norm source1 w] cu 2 rank := by
  have hr : rank = 0 ∨ rank = 1 := by omega
  have hlocal : ([source0, source1].getD rank (zeroTensor [])).shape =
      [lDim, hidden] := by
    rcases hr with rfl | rfl <;> simp [List.getD, hs0, hs1]
  have hrs0 := fw_rms_norm_shape_2d source0 w lDim hidden hs0
  have hrs1 := fw_rms_norm_shape_2d source1 w lDim hidden hs1
  have hlocalRms :
      ([fw_rms_norm source0 w, fw_rms_norm source1 w].getD rank
        (zeroTensor [])).shape = [lDim, hidden] := by
    rcases hr with rfl | rfl <;> simp [List.getD, hrs0, hrs1]
  have hsL :
      (fw_rms_norm
        (fw_maybe_shuffle_collective [source0, source1] cu 2 rank) w).shape =
        [lDim, hidden] :=
    fw_rms_norm_shape_2d _ _ lDim hidden
      (by rw [fw_maybe_shuffle_collective_shape]; exact hlocal)
  apply Tensor.ext
  · rw [fw_rms_norm_shape_2d _ _ lDim hidden
        (by rw [fw_maybe_shuffle_collective_shape]; exact hlocal),
      fw_maybe_shuffle_collective_shape, hlocalRms]
  · intro idx hidx
    have hidxBound : idx < lDim * hidden := by
      rw [hsL] at hidx
      simpa [prodShape] using hidx
    let row := idx / hidden
    let j := idx % hidden
    have hrow : row < lDim := by
      dsimp [row]
      exact Nat.div_lt_iff_lt_mul hh |>.mpr (by simpa [Nat.mul_comm] using hidxBound)
    have hj : j < hidden := by
      dsimp [j]
      exact Nat.mod_lt _ hh
    let global := zigzagPos cu 2 rank row
    let srcRank := global / lDim
    let srcRow := global % lDim
    have hsrcRow : srcRow < lDim := by
      dsimp [srcRow]
      exact Nat.mod_lt _ hl
    have hidxEq : idx = row * hidden + j := by
      dsimp [row, j]
      calc
        idx = hidden * (idx / hidden) + idx % hidden :=
          (Nat.div_add_mod idx hidden).symm
        _ = idx / hidden * hidden + idx % hidden := by ring
    have hrowIndex (k : Nat) (hk : k < hidden) :
        row * hidden + k < lDim * hidden := by
      have hlt : row * hidden + k < row * hidden + hidden :=
        Nat.add_lt_add_left hk _
      have hle : (row + 1) * hidden ≤ lDim * hidden :=
        Nat.mul_le_mul_right hidden (by omega)
      rw [show row * hidden + hidden = (row + 1) * hidden by ring] at hlt
      exact lt_of_lt_of_le hlt hle
    have hshuffle (k : Nat) (hk : k < hidden) :
        valAt (fw_maybe_shuffle_collective [source0, source1] cu 2 rank)
            (row * hidden + k) =
          valAt ([source0, source1].getD srcRank (zeroTensor []))
            (srcRow * hidden + k) := by
      rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by omega)]
      · simp only [hlocal, List.tail_cons, prodShape,
          List.foldl, Nat.mul_one, Nat.one_mul]
        rw [show row * hidden + k = k + hidden * row by ring,
          Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hk, Nat.zero_add,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
        rfl
      · rw [hlocal]
        simpa [prodShape] using hrowIndex k hk
    have hmean :
        rmsMeanSqAt (fw_maybe_shuffle_collective [source0, source1] cu 2 rank)
            row hidden =
          rmsMeanSqAt ([source0, source1].getD srcRank (zeroTensor []))
            srcRow hidden := by
      unfold rmsMeanSqAt
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [hshuffle k hk]
    rw [hidxEq]
    have hleft :
        valAt (fw_rms_norm
          (fw_maybe_shuffle_collective [source0, source1] cu 2 rank) w)
          (row * hidden + j) =
        (valAt ([source0, source1].getD srcRank (zeroTensor []))
            (srcRow * hidden + j) *
          (1 / sqrtFn (rmsMeanSqAt
            ([source0, source1].getD srcRank (zeroTensor []))
              srcRow hidden + rmsNormEps))) * valAt w j := by
      rw [fw_rms_norm_valAt_2d _ _ lDim hidden _
        (by rw [fw_maybe_shuffle_collective_shape]; exact hlocal)
        (hrowIndex j hj)]
      rw [hshuffle j hj]
      rw [show row * hidden + j = j + hidden * row by ring,
        Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hj, Nat.zero_add,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
      rw [hmean]
    rw [hleft]
    rw [fw_maybe_shuffle_collective_valAt _ _ 2 rank _ (by omega)]
    · simp only [hlocalRms, List.tail_cons, prodShape,
        List.foldl, Nat.mul_one, Nat.one_mul]
      rw [show row * hidden + j = j + hidden * row by ring,
        Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hj, Nat.zero_add,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
      unfold gatherFromRank
      dsimp only [srcRank, srcRow, global]
      change
        valAt ([source0, source1].getD (global / lDim) (zeroTensor []))
              (global % lDim * hidden + j) *
            (1 / sqrtFn (rmsMeanSqAt
              ([source0, source1].getD (global / lDim) (zeroTensor []))
                (global % lDim) hidden + rmsNormEps)) * valAt w j =
          valAt ([fw_rms_norm source0 w, fw_rms_norm source1 w].getD
            (global / lDim) (zeroTensor []))
            (global % lDim * hidden + j)
      by_cases hsr0 : global / lDim = 0
      · simp only [hsr0, List.getD, List.getElem?_cons_zero, Option.getD_some]
        have hib : global % lDim * hidden + j < lDim * hidden := by
          have hlt : global % lDim * hidden + j <
              global % lDim * hidden + hidden := Nat.add_lt_add_left hj _
          have hle : (global % lDim + 1) * hidden ≤ lDim * hidden :=
            Nat.mul_le_mul_right hidden (by omega)
          rw [show global % lDim * hidden + hidden =
            (global % lDim + 1) * hidden by ring] at hlt
          exact lt_of_lt_of_le hlt hle
        rw [fw_rms_norm_valAt_2d source0 w lDim hidden _ hs0 hib]
        simp [show global % lDim * hidden + j =
            j + hidden * (global % lDim) by ring,
          Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hj,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
      · by_cases hsr1 : global / lDim = 1
        · simp only [hsr1, List.getD, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.getD_some]
          have hib : global % lDim * hidden + j < lDim * hidden := by
            have hlt : global % lDim * hidden + j <
                global % lDim * hidden + hidden := Nat.add_lt_add_left hj _
            have hle : (global % lDim + 1) * hidden ≤ lDim * hidden :=
              Nat.mul_le_mul_right hidden (by omega)
            rw [show global % lDim * hidden + hidden =
              (global % lDim + 1) * hidden by ring] at hlt
            exact lt_of_lt_of_le hlt hle
          rw [fw_rms_norm_valAt_2d source1 w lDim hidden _ hs1 hib]
          simp [show global % lDim * hidden + j =
              j + hidden * (global % lDim) by ring,
            Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hj,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
        · have hnot : ¬ global / lDim < 2 := by
            intro hlt
            cases hq : global / lDim with
            | zero => exact hsr0 hq
            | succ q =>
              cases q with
              | zero => exact hsr1 hq
              | succ q =>
                rw [hq] at hlt
                exact (Nat.not_lt_of_ge
                  (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le q)))) hlt
          have hget : [source0, source1].getD (global / lDim) (zeroTensor []) =
              zeroTensor [] := by
            simp [List.getD, hnot]
          have hgetR :
              [fw_rms_norm source0 w, fw_rms_norm source1 w].getD
                (global / lDim) (zeroTensor []) = zeroTensor [] := by
            simp [List.getD, hnot]
          rw [hget, hgetR]
          simp only [valAt_zeroTensor_empty, zero_mul]
    · rw [hlocalRms]
      simpa [prodShape] using hrowIndex j hj

end
end TrainVerify.Denote.ZigzagCollective
