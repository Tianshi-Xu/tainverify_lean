import denote.ZigzagKExit
import denote.ZigzagKRelationWitness

namespace TrainVerify.Denote.RelationCompiler.ZigzagKExitWitness

open ZigzagCollective ZigzagKRelationWitness

noncomputable section

/-- Exit consumes every actual CP3 entry output in semantic rank order. -/
def exits : List Tensor :=
  (List.range 3).map (fun rank =>
    fw_maybe_unshuffle_collective [out 0, out 1, out 2]
      (decodeCuSeqlens cu) 3 rank)

/-- Backward shuffle uses the genuine backward collective, not a stand-in. -/
def bwExits : List Tensor :=
  (List.range 3).map (fun rank =>
    bw_maybe_shuffle_collective [out 0, out 1, out 2]
      (decodeCuSeqlens cu) 3 rank)

/-- Complete tensor-list equality, including all lanes, shapes and the last rank,
for the existing asymmetric sources [1..8], [101..108], [201..208]. -/
theorem exits_eq_sources : exits = sources := by
  have h := unshuffle_shuffle_single_list sources 3 2 [2]
    (by decide) (by decide) rfl sharded_input.shard_shapes
  rw [← decode_cu] at h
  exact h

/-- Apply the relation exit to the inhabited entry, not a new source model. -/
theorem sharded_exit : ShardedRel full exits 0 [12, 2] [4, 2] := by
  exact entry.to_sharded_unshuffle_single (d := 2) (tail := [2])
    (by decide) decode_cu

theorem bwExits_eq_sources : bwExits = sources := by
  unfold bwExits
  simp only [bw_maybe_shuffle_collective_eq_fw_unshuffle]
  exact exits_eq_sources

theorem sharded_bw_exit : ShardedRel full bwExits 0 [12, 2] [4, 2] := by
  exact entry.to_sharded_bw_shuffle_single (d := 2) (tail := [2])
    (by decide) decode_cu

/-- One concrete inhabitant simultaneously supplies the entry, singleton metadata,
complete source recovery and the full ordinary relation for both exit aliases. -/
theorem cp3_exit_witness :
    ZigzagKRel full [out 0, out 1, out 2] cu [12, 2] [4, 2] ∧
    decodeCuSeqlens cu = [0, 12] ∧
    exits = sources ∧ ShardedRel full exits 0 [12, 2] [4, 2] ∧
    bwExits = sources ∧ ShardedRel full bwExits 0 [12, 2] [4, 2] :=
  ⟨entry, decode_cu, exits_eq_sources, sharded_exit,
    bwExits_eq_sources, sharded_bw_exit⟩

/-- Conditional K1 caller: the complete list follows the singleton branch. -/
theorem cp1_roundtrip (xs : List Tensor)
    (hlen : xs.length = 1) (hshape : ∀ x ∈ xs, x.shape = [2]) :
    ((List.range 1).map (fun rank =>
      fw_maybe_unshuffle_collective
        ((List.range 1).map (fw_maybe_shuffle_collective xs [0, 2] 1))
        [0, 2] 1 rank)) = xs := by
  exact unshuffle_shuffle_single_list xs 1 1 []
    (by decide) (by decide) hlen hshape

/-- Conditional K5 caller with the same shapes as the existing inverse witness. -/
theorem cp5_roundtrip (xs : List Tensor)
    (hlen : xs.length = 5) (hshape : ∀ x ∈ xs, x.shape = [2, 3]) :
    ((List.range 5).map (fun rank =>
      fw_maybe_unshuffle_collective
        ((List.range 5).map (fw_maybe_shuffle_collective xs [0, 10] 5))
        [0, 10] 5 rank)) = xs := by
  exact unshuffle_shuffle_single_list xs 5 1 [3]
    (by decide) (by decide) hlen hshape

/-- A zero-volume tail needs no positive-stride assumption. -/
theorem zero_volume_roundtrip (xs : List Tensor) (K d : Nat)
    (hK : 0 < K) (hd : 0 < d) (hlen : xs.length = K)
    (hshape : ∀ x ∈ xs, x.shape = [2 * d, 0]) :
    ((List.range K).map (fun rank =>
      fw_maybe_unshuffle_collective
        ((List.range K).map (fw_maybe_shuffle_collective xs [0, K * (2 * d)] K))
        [0, K * (2 * d)] K rank)) = xs := by
  exact unshuffle_shuffle_single_list xs K d [0] hK hd hlen hshape

end
end TrainVerify.Denote.RelationCompiler.ZigzagKExitWitness
