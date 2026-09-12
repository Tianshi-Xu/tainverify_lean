import denote.SourceBWLayernormDgammaUnit

/-! D=3, B=2, S=3, H=5: genuinely valued DP inputs.
G varies by position/rank, X has nonconstant rows with rank-dependent curvature
relative to its linear term, and shared gamma is nonconstant. Both full inputs
are the actual axis-0 gathers. No output relation is assumed.
Edit-only candidate: the parent runs numeric and serial kernel/audit gates.
-/
namespace TrainVerify.Denote.DgammaUnitWitness
noncomputable section

private def gpart (r : Nat) : Tensor :=
  Tensor.mkShape [2, 3, 5] (fun i => ((100 * r + i.1 + 1 : Nat) : Scalar))

private def xpart (r : Nat) : Tensor :=
  Tensor.mkShape [2, 3, 5]
    (fun i => ((20 * r + i.1 * i.1 + (r + 1) * i.1 : Nat) : Scalar))

private def gamma : Tensor :=
  Tensor.mkShape [5] (fun i => ((2 + i.1 : Nat) : Scalar))

private def beta : Tensor :=
  Tensor.mkShape [5] (fun i => ((7 + i.1 : Nat) : Scalar))

private def gs : List Tensor := [gpart 0, gpart 1, gpart 2]
private def xs : List Tensor := [xpart 0, xpart 1, xpart 2]
private def fullG : Tensor := allGatherPrimDimN 0 3 0 gs
private def fullX : Tensor := allGatherPrimDimN 0 3 0 xs
private def locals : List Tensor :=
  List.zipWith (fun g x => (bw_layernorm g x gamma beta).2.1) gs xs

private theorem gs_shapes : ∀ t ∈ gs, t.shape = [2, 3, 5] := by
  intro t ht
  simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> rfl

private theorem xs_shapes : ∀ t ∈ xs, t.shape = [2, 3, 5] := by
  intro t ht
  simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> rfl

private theorem fullG_shape : fullG.shape = [6, 3, 5] := by
  unfold fullG
  rw [allGatherPrimDimN_shape 0 3 gs [2, 3, 5] (by rfl)]
  rfl

private theorem fullX_shape : fullX.shape = [6, 3, 5] := by
  unfold fullX
  rw [allGatherPrimDimN_shape 0 3 xs [2, 3, 5] (by rfl)]
  rfl

/-- Complete inhabited input contract: two correctly shaped/value-faithful gathers,
exact rank counts, complete shared parameters, and positive dimensions. -/
theorem input_contract :
    (0 < (3 : Nat) ∧ 0 < (2 : Nat) ∧ 0 < (3 : Nat) ∧ 0 < (5 : Nat)) ∧
    fullG.shape = [6, 3, 5] ∧ fullX.shape = [6, 3, 5] ∧
    gs.length = 3 ∧ xs.length = 3 ∧
    (∀ t ∈ gs, t.shape = [2, 3, 5]) ∧ (∀ t ∈ xs, t.shape = [2, 3, 5]) ∧
    gamma.shape = [5] ∧ beta.shape = [5] ∧
    fullG = allGatherPrimDimN 0 3 0 gs ∧ fullX = allGatherPrimDimN 0 3 0 xs := by
  exact ⟨by decide, fullG_shape, fullX_shape, rfl, rfl,
    gs_shapes, xs_shapes, rfl, rfl, rfl, rfl⟩

/-- Generic DP theorem applied to the concrete nondegenerate inputs. -/
theorem batch_reduction :
    (bw_layernorm fullG fullX gamma beta).2.1 = tensorSum locals :=
  source_bw_layernorm_dgamma_batch_reduction 3 2 3 5 fullG fullX gamma beta gs xs
    (by decide) (by decide) (by decide) (by decide)
    fullG_shape fullX_shape rfl rfl gs_shapes xs_shapes rfl rfl rfl rfl

theorem output_shapes :
    (bw_layernorm fullG fullX gamma beta).2.1.shape = [5] ∧
    (tensorSum locals).shape = [5] ∧
    (∀ t ∈ locals, t.shape = [5]) := by
  have hout : (bw_layernorm fullG fullX gamma beta).2.1.shape = [5] :=
    (bw_layernorm_dw_shape fullG fullX gamma beta 5 [3, 6]
      (by rw [fullX_shape]; rfl)).trans rfl
  refine ⟨hout, ?_, ?_⟩
  · rw [← batch_reduction]
    exact hout
  · intro t ht
    change t ∈ [(bw_layernorm (gpart 0) (xpart 0) gamma beta).2.1,
      (bw_layernorm (gpart 1) (xpart 1) gamma beta).2.1,
      (bw_layernorm (gpart 2) (xpart 2) gamma beta).2.1] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact (bw_layernorm_dw_shape _ _ gamma beta 5 [3, 2] rfl).trans rfl
    · exact (bw_layernorm_dw_shape _ _ gamma beta 5 [3, 2] rfl).trans rfl
    · exact (bw_layernorm_dw_shape _ _ gamma beta 5 [3, 2] rfl).trans rfl

theorem cotangent_nonconstant : valAt (gpart 0) 0 ≠ valAt (gpart 0) 1 := by
  change ((1 : Nat) : Scalar) ≠ ((2 : Nat) : Scalar)
  norm_num

theorem saved_row_nonconstant : valAt (xpart 0) 0 ≠ valAt (xpart 0) 1 := by
  change ((0 : Nat) : Scalar) ≠ ((2 : Nat) : Scalar)
  norm_num

theorem gamma_nonconstant : valAt gamma 0 ≠ valAt gamma 1 := by
  change (2 : Scalar) ≠ 3
  norm_num

theorem rank_inputs_differ :
    valAt (gpart 0) 0 ≠ valAt (gpart 1) 0 ∧
    valAt (xpart 0) 0 ≠ valAt (xpart 1) 0 := by
  change ((1 : Nat) : Scalar) ≠ ((101 : Nat) : Scalar) ∧
    ((0 : Nat) : Scalar) ≠ ((20 : Nat) : Scalar)
  norm_num

-- Saved rows differ in their adjacent increments, not only a constant offset.
theorem saved_rank_row_increments_differ :
    valAt (xpart 0) 1 - valAt (xpart 0) 0 ≠
      valAt (xpart 1) 1 - valAt (xpart 1) 0 := by
  change ((2 : Nat) : Scalar) - ((0 : Nat) : Scalar) ≠
    ((23 : Nat) : Scalar) - ((20 : Nat) : Scalar)
  norm_num

#print axioms input_contract
#print axioms batch_reduction
#print axioms output_shapes
#print axioms cotangent_nonconstant
#print axioms saved_row_nonconstant
#print axioms gamma_nonconstant
#print axioms rank_inputs_differ
#print axioms saved_rank_row_increments_differ

end
end TrainVerify.Denote.DgammaUnitWitness
