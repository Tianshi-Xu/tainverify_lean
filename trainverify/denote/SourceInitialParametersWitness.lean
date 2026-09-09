import denote.SourceInitialParameters

namespace TrainVerify.Denote.SourceInitialParametersWitness
open RelationCompiler SourceInitialParameters
set_option maxHeartbeats 500000
noncomputable section

/-- Concrete first embedding, ordered DP unit [16,319]. -/
theorem embedding_unit0
    (initSM initPM : Store)
    (hfull : (initSM 1212).shape = [256, 64])
    (h16 : initPM 16 = chunkPrimDimN 1 2 0 (initSM 1212))
    (h319 : initPM 319 = chunkPrimDimN 1 2 1 (initSM 1212)) :
    RelationFact.Holds (.sharded 1212 [16, 319] 1 [256, 64] [256, 32]) initSM initPM := by
  apply sharded_of_exact_slices initSM initPM 1212 [16, 319] 1 2
    [256, 64] [256, 32] (by decide) (by decide) hfull (by decide)
  change [initPM 16, initPM 319] =
    [chunkPrimDimN 1 2 0 (initSM 1212), chunkPrimDimN 1 2 1 (initSM 1212)]
  rw [h16, h319]

/-- Concrete first embedding, independent ordered DP unit [622,925]. -/
theorem embedding_unit1
    (initSM initPM : Store)
    (hfull : (initSM 1212).shape = [256, 64])
    (h622 : initPM 622 = chunkPrimDimN 1 2 0 (initSM 1212))
    (h925 : initPM 925 = chunkPrimDimN 1 2 1 (initSM 1212)) :
    RelationFact.Holds (.sharded 1212 [622, 925] 1 [256, 64] [256, 32]) initSM initPM := by
  apply sharded_of_exact_slices initSM initPM 1212 [622, 925] 1 2
    [256, 64] [256, 32] (by decide) (by decide) hfull (by decide)
  change [initPM 622, initPM 925] =
    [chunkPrimDimN 1 2 0 (initSM 1212), chunkPrimDimN 1 2 1 (initSM 1212)]
  rw [h622, h925]


/-- A mathematical witness only; not a deserialization of captured parameters.
The two independent units share slice 0 and slice 1, respectively. -/
def embeddingPM (weight : Tensor) : Store := fun tid =>
  if tid = 16 ∨ tid = 622 then chunkPrimDimN 1 2 0 weight
  else chunkPrimDimN 1 2 1 weight

/-- Every full embedding tensor of the required shape admits both sets of exact
caller equations simultaneously, together with both separate typed relations. -/
theorem embedding_inputs_nonvacuous (weight : Tensor)
    (hweight : weight.shape = [256, 64]) :
    ∃ initSM initPM : Store,
      initSM 1212 = weight ∧
      (initSM 1212).shape = [256, 64] ∧
      initPM 16 = chunkPrimDimN 1 2 0 (initSM 1212) ∧
      initPM 319 = chunkPrimDimN 1 2 1 (initSM 1212) ∧
      initPM 622 = chunkPrimDimN 1 2 0 (initSM 1212) ∧
      initPM 925 = chunkPrimDimN 1 2 1 (initSM 1212) ∧
      RelationFact.Holds (.sharded 1212 [16, 319] 1 [256, 64] [256, 32]) initSM initPM ∧
      RelationFact.Holds (.sharded 1212 [622, 925] 1 [256, 64] [256, 32]) initSM initPM := by
  refine ⟨(fun _ => weight), embeddingPM weight, rfl, hweight,
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact embedding_unit0 _ _ hweight rfl rfl
  · exact embedding_unit1 _ _ hweight rfl rfl

/-- The shape premise itself is inhabited by a nonzero mathematical tensor. -/
def weightOnes : Tensor := Tensor.mkShape [256, 64] (fun _ => 1)

theorem weightOnes_shape : weightOnes.shape = [256, 64] := rfl

-- Parent compile probe: dependency footprints must be a subset of kernel3.
#print axioms SourceInitialParameters.chunked_of_exact_slices
#print axioms SourceInitialParameters.sharded_of_exact_slices
#print axioms SourceInitialParameters.replicated_of_exact_values
#print axioms embedding_unit0
#print axioms embedding_unit1
#print axioms embedding_inputs_nonvacuous
#check embedding_inputs_nonvacuous weightOnes weightOnes_shape

end
end TrainVerify.Denote.SourceInitialParametersWitness
