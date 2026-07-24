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

end
end TrainVerify.Denote.ZigzagCollective
