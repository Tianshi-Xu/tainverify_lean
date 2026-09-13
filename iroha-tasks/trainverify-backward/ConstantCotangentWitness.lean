import denote.SourceConstantCotangent

/-!
Non-unit seed witness: D = K = 3, DP unit = TP destination = 2,
with asymmetric local dimensions B = 2, S = 5, O = 7.
The terms below really run BW_sum, batch chunk, hidden gather, and faithful
AA(1,2), rather than defining their outputs to be the desired constants.
-/
namespace TrainVerify.Denote.ConstantCotangentWitness
noncomputable section

abbrev seed : Tensor := sourceConstantCotangent [1] (3 : Scalar)
abbrev saved : Tensor := zeroTensor [6, 5, 7]
abbrev broadcast : Tensor := bw_sum seed saved
abbrev localCotangent : Tensor := chunkPrimDimN 0 3 2 broadcast
abbrev gathered : Tensor := allGatherPrimDimN 2 3 0 (List.replicate 3 localCotangent)
abbrev exchanged : Tensor :=
  AllToAllSourceFaithful.tensor 3 2 1 2 (List.replicate 3 gathered)

theorem seed_value : valAt seed 0 = (3 : Scalar) :=
  source_constant_valAt [1] 3 0 (by decide)

theorem seed_nonunit : valAt seed 0 ≠ (1 : Scalar) := by
  rw [seed_value]
  norm_num

theorem broadcast_value : broadcast = sourceConstantCotangent [6, 5, 7] (3 : Scalar) := by
  change bw_sum seed saved = _
  rw [source_constant_bw_sum, seed_value]
  rfl

theorem chunk_value : localCotangent = sourceConstantCotangent [2, 5, 7] (3 : Scalar) := by
  change chunkPrimDimN 0 3 2 broadcast = _
  rw [broadcast_value]
  exact source_constant_chunk0_rank3 3 2 5 7 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem gather_value : gathered = sourceConstantCotangent [2, 5, 21] (3 : Scalar) := by
  change allGatherPrimDimN 2 3 0 (List.replicate 3 localCotangent) = _
  rw [chunk_value]
  exact source_constant_gather2_rank3 3 2 5 7 3
    (by decide) (by decide) (by decide) (by decide)

theorem faithful_alltoall_value :
    exchanged = sourceConstantCotangent [2, 15, 7] (3 : Scalar) := by
  change AllToAllSourceFaithful.tensor 3 2 1 2 (List.replicate 3 gathered) = _
  rw [gather_value]
  exact source_constant_alltoall12_rank3 3 2 5 7 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Shapes are conclusions about the actual chain, not input assumptions. -/
theorem actual_shapes :
    broadcast.shape = [6, 5, 7] ∧ localCotangent.shape = [2, 5, 7] ∧
    gathered.shape = [2, 5, 21] ∧ exchanged.shape = [2, 15, 7] := by
  rw [broadcast_value, chunk_value, gather_value, faithful_alltoall_value]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem actual_values (i : Nat) (hi : i < prodShape [2, 15, 7]) :
    valAt exchanged i = (3 : Scalar) := by
  rw [faithful_alltoall_value]
  exact source_constant_valAt _ _ _ hi

/-- An interior value, as well as the universal in-bounds value theorem. -/
theorem actual_value_137 : valAt exchanged 137 = (3 : Scalar) :=
  actual_values 137 (by decide)

#print axioms seed_value
#print axioms seed_nonunit
#print axioms broadcast_value
#print axioms chunk_value
#print axioms gather_value
#print axioms faithful_alltoall_value
#print axioms actual_shapes
#print axioms actual_values
#print axioms actual_value_137

end
end TrainVerify.Denote.ConstantCotangentWitness
