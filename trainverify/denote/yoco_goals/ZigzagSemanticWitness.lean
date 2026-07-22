/-
Concrete, zero-axiom regression witnesses for the YOCO cp=2 zigzag contract.

The Python authority calls `zigzag_allgather_attn_varlen`: Q/output ownership is
zigzag, while K and V entering that call are already replicated full-sequence
inputs on both ranks.  Therefore concatenating buddy K/V is not reconstruction;
it duplicates an already-full sequence.  This module records those facts
without changing the production Denote semantics.
-/

import denote.Denote

open TrainVerify.Denote

namespace TrainVerify.Denote.YocoZigzagSemanticWitness

/-- Four distinguishable scalar positions, flattened as a one-dimensional Tensor. -/
def positions4 : Tensor :=
  Tensor.mkShape [4] (fun i => (i.val : Scalar))

/-- The ordinary rank-0 contiguous chunk selects global positions `[0, 1]`. -/
def contiguousRank0 : Tensor :=
  Tensor.mkShape [2] (fun i => positions4.val ⟨i.val, by
    have hi := i.isLt
    simp [positions4, Tensor.mkShape, prodShape] at hi ⊢
    omega⟩)

/-- Correct cp=2 zigzag rank-0 ownership selects global positions `[0, 3]`. -/
def zigzagRank0 : Tensor :=
  Tensor.mkShape [2] (fun i => positions4.val ⟨3 * i.val, by
    have hi := i.isLt
    simp [positions4, Tensor.mkShape, prodShape] at hi ⊢
    omega⟩)

/-- Correct cp=2 zigzag rank-1 ownership selects global positions `[1, 2]`. -/
def zigzagRank1 : Tensor :=
  Tensor.mkShape [2] (fun i => positions4.val ⟨1 + i.val, by
    have hi := i.isLt
    simp [positions4, Tensor.mkShape, prodShape] at hi ⊢
    omega⟩)

/-- The same output shape hides a concrete value mismatch at local offset one. -/
theorem contiguous_rank0_value_one : valAt contiguousRank0 1 = 1 := by
  change ((1 : Nat) : Scalar) = 1
  norm_num

/-- Rank 0's correct zigzag second output comes from global position three. -/
theorem zigzag_rank0_value_one : valAt zigzagRank0 1 = 3 := by
  change ((3 : Nat) : Scalar) = 3
  norm_num

/-- Ordinary contiguous rank chunk selection is not cp=2 zigzag selection. -/
theorem contiguous_rank0_ne_zigzag_rank0 : contiguousRank0 ≠ zigzagRank0 := by
  intro h
  have hv := congrArg (fun t => valAt t 1) h
  rw [contiguous_rank0_value_one, zigzag_rank0_value_one] at hv
  norm_num at hv

/-- The complete minimal cp=2 ownership vector is rank0 `[0,3]`, rank1 `[1,2]`. -/
theorem cp2_zigzag_position_vector :
    valAt zigzagRank0 0 = 0 ∧ valAt zigzagRank0 1 = 3 ∧
    valAt zigzagRank1 0 = 1 ∧ valAt zigzagRank1 1 = 2 := by
  change
    ((0 : Nat) : Scalar) = 0 ∧ ((3 : Nat) : Scalar) = 3 ∧
    ((1 : Nat) : Scalar) = 1 ∧ ((2 : Nat) : Scalar) = 2
  norm_num

/-- YOCO supplies each cp rank with the same already-full K/V pair.  This is a
    semantic input contract, not a request to gather sequence shards. -/
def replicatedFullKV (k v : Tensor) : List (Tensor × Tensor) :=
  [(k, v), (k, v)]

/-- Executable documentation of the cp=2 replicated-full K/V contract. -/
theorem replicated_full_kv_vector (k v : Tensor) :
    replicatedFullKV k v = [(k, v), (k, v)] := by
  rfl

/-- Gathering two replicated full length-four K copies produces length eight,
    proving by shape alone that such a gather is not identity. -/
theorem gather_duplicated_full_k_shape :
    (allGatherPrimDimN 0 2 0 [positions4, positions4]).shape = [8] := by
  rfl

/-- Value/shape witness: gathering duplicated full K is not the original K. -/
theorem gather_duplicated_full_k_ne_identity :
    allGatherPrimDimN 0 2 0 [positions4, positions4] ≠ positions4 := by
  intro h
  have hshape := congrArg Tensor.shape h
  rw [gather_duplicated_full_k_shape] at hshape
  norm_num [positions4, Tensor.mkShape] at hshape

end TrainVerify.Denote.YocoZigzagSemanticWitness
