import denote.KRankZigzagSingle

open TrainVerify.Denote TrainVerify.Denote.ZigzagCollective
namespace TrainVerify.Denote.KRankZigzagSingleWitness

-- Permutation-sensitive CP3 map: rank order is deliberately not global order.
theorem cp3_positions :
    (List.range 3).map (fun r => (List.range 2).map (zigzagPos [0, 6] 3 r)) =
      [[0, 5], [1, 4], [2, 3]] := by
  rfl

theorem cp3_gather_is_not_canonical :
    ((List.range 3).map (fun r => (List.range 2).map (zigzagPos [0, 6] 3 r))).flatten ≠
      List.range 6 := by
  rw [cp3_positions]
  decide

-- All ranks and all data values, with a nontrivial two-dimensional tail.
theorem cp3_roundtrip (xs : List Tensor) (r : Nat)
    (hlen : xs.length = 3) (hr : r < 3)
    (hshape : ∀ x ∈ xs, x.shape = [10, 2, 7]) :
    fw_maybe_unshuffle_collective
      ((List.range 3).map (fw_maybe_shuffle_collective xs [0, 30] 3))
      [0, 30] 3 r = xs.getD r (zeroTensor []) := by
  exact fw_maybe_unshuffle_shuffle_collective_single xs 3 5 r [2, 7]
    (by decide) (by decide) hr hlen hshape

theorem cp5_roundtrip (xs : List Tensor) (r : Nat)
    (hlen : xs.length = 5) (hr : r < 5)
    (hshape : ∀ x ∈ xs, x.shape = [2, 3]) :
    fw_maybe_unshuffle_collective
      ((List.range 5).map (fw_maybe_shuffle_collective xs [0, 10] 5))
      [0, 10] 5 r = xs.getD r (zeroTensor []) := by
  exact fw_maybe_unshuffle_shuffle_collective_single xs 5 1 r [3]
    (by decide) (by decide) hr hlen hshape

theorem cp1_roundtrip (xs : List Tensor)
    (hlen : xs.length = 1) (hshape : ∀ x ∈ xs, x.shape = [2]) :
    fw_maybe_unshuffle_collective
      ((List.range 1).map (fw_maybe_shuffle_collective xs [0, 2] 1))
      [0, 2] 1 0 = xs.getD 0 (zeroTensor []) := by
  exact fw_maybe_unshuffle_shuffle_collective_single xs 1 1 0 []
    (by decide) (by decide) (by decide) hlen hshape

-- Shape hypotheses are inhabited by position-distinguishing tensors.
noncomputable def labeledShard (r : Nat) : Tensor :=
  Tensor.mkShape [10, 2, 7] (fun i => ((r * 140 + i.val : Nat) : Scalar))

theorem cp3_witness_inputs : ∃ xs : List Tensor,
    xs.length = 3 ∧ (∀ x ∈ xs, x.shape = [10, 2, 7]) := by
  refine ⟨(List.range 3).map labeledShard, ?_, ?_⟩
  · simp only [List.length_map, List.length_range]
  · intro x hx
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    rfl

end TrainVerify.Denote.KRankZigzagSingleWitness
