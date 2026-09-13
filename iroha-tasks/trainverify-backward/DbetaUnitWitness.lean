import denote.SourceBWLayernormDbetaUnit

/-! K=3, B=2, S=3, H=2 input-contract witness.
The cotangent is position/rank dependent. Saved-X, gamma and beta differ
between ranks and from the full invocation. No output equation is assumed.
The parent serial kernel gate checks this witness with the generic adapter. -/
namespace TrainVerify.Denote.DbetaUnitWitness
noncomputable section

private def ramp (sh : Shape) (offset : Nat) : Tensor :=
  Tensor.mkShape sh (fun i => ((offset + i.1 : Nat) : Scalar))

private def piece (r : Nat) : DbetaSourceInput :=
  { g := ramp [2, 3, 2] (100 * r)
    x := ramp [2, 3, 2] (1000 + r)
    gamma := ramp [2] (20 + r)
    beta := ramp [2] (50 + r) }

private def pieces : List DbetaSourceInput := [piece 0, piece 1, piece 2]

private def full : DbetaSourceInput :=
  { g := allGatherPrimDimN 0 3 0 (pieces.map DbetaSourceInput.g)
    x := ramp [6, 3, 2] 9000
    gamma := ramp [2] 200
    beta := ramp [2] 500 }

private theorem piece_shapes (r : Nat) : (piece r).Shaped 2 3 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem full_shapes : full.Shaped (2 * 3) 3 2 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  change (allGatherPrimDimN 0 3 0 (pieces.map DbetaSourceInput.g)).shape = [2 * 3, 3, 2]
  rw [allGatherPrimDimN_shape 0 3 (pieces.map DbetaSourceInput.g) [2, 3, 2] (by rfl)]
  rfl

/-- Explicitly inhabited complete source contract, including exact list length. -/
theorem input_contract :
    full.Shaped 6 3 2 ∧ pieces.length = 3 ∧
      (∀ p ∈ pieces, p.Shaped 2 3 2) ∧
      full.g = allGatherPrimDimN 0 3 0 (pieces.map DbetaSourceInput.g) := by
  refine ⟨full_shapes, rfl, ?_, rfl⟩
  intro p hp
  simp only [pieces, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact piece_shapes _

/-- Actual nonconstant-G arbitrary-K DP theorem application. -/
theorem batch_reduction : full.output = tensorSum (pieces.map DbetaSourceInput.output) :=
  source_bw_layernorm_dbeta_batch_reduction 3 2 3 2 full pieces
    (by decide) (by decide) (by decide) (by decide)
    input_contract.1 input_contract.2.1 input_contract.2.2.1 input_contract.2.2.2

theorem cotangent_nonconstant : valAt (piece 0).g 0 ≠ valAt (piece 0).g 1 := by
  change ((0 : Nat) : Scalar) ≠ ((1 : Nat) : Scalar)
  norm_num

theorem rank_cotangents_differ : valAt (piece 0).g 0 ≠ valAt (piece 1).g 0 := by
  change ((0 : Nat) : Scalar) ≠ ((100 : Nat) : Scalar)
  norm_num

theorem saved_values_differ :
    valAt (piece 0).x 0 ≠ valAt (piece 1).x 0 ∧
    valAt (piece 0).gamma 0 ≠ valAt (piece 1).gamma 0 ∧
    valAt (piece 0).beta 0 ≠ valAt (piece 1).beta 0 := by
  change (1000 : Scalar) ≠ 1001 ∧ (20 : Scalar) ≠ 21 ∧ (50 : Scalar) ≠ 51
  norm_num

theorem saved_value_replacement :
    (bw_layernorm (piece 0).g (piece 0).x (piece 0).gamma (piece 0).beta).2.2 =
      (bw_layernorm (piece 0).g (piece 1).x (piece 1).gamma (piece 1).beta).2.2 :=
  bw_layernorm_dbeta_shape_only _ _ _ _ _ _ _ 2 [3, 2] rfl rfl rfl rfl

#print axioms input_contract
#print axioms batch_reduction
#print axioms cotangent_nonconstant
#print axioms rank_cotangents_differ
#print axioms saved_values_differ
#print axioms saved_value_replacement

end
end TrainVerify.Denote.DbetaUnitWitness
