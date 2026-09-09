import denote.SourceEmbeddingBatch

/-! UNCOMPILED CANDIDATE. Parent compile/axiom probe; no runtime refinement claim. -/
namespace TrainVerify.Denote
noncomputable section
set_option maxHeartbeats 500000

-- Exact current source dimensions, either DP unit, with arbitrary tensor values.
example (unit : Nat) (ids piece weight : Tensor) (hu : unit < 2)
    (hi : ids.shape = [2, 16]) (hw : weight.shape = [256, 32])
    (hp : piece = chunkPrimDimN 0 2 unit ids) :
    fw_embedding piece weight = chunkPrimDimN 0 2 unit (fw_embedding ids weight) :=
  fw_embedding_batch_chunk_dim0 2 unit 1 16 256 32 ids piece weight
    (by decide) hu (by decide) (by decide) hi hw hp

-- The source-dimensional input premises are satisfiable; no output relation
-- is hidden in this witness or required by the generic theorem.
example : ∃ ids piece weight : Tensor,
    ids.shape = [2, 16] ∧ weight.shape = [256, 32] ∧
    piece = chunkPrimDimN 0 2 1 ids := by
  refine ⟨zeroTensor [2, 16], chunkPrimDimN 0 2 1 (zeroTensor [2, 16]),
    zeroTensor [256, 32], rfl, rfl, rfl⟩

#check fw_embedding_batch_chunk_dim0
#print axioms fw_embedding_batch_chunk_dim0

end
end TrainVerify.Denote
