import denote.SourceBWLinearDxUnit

/-!
Satisfiability witness, deliberately separate from production roots.
D=2, T=3, B=1, S=2, O=1, I=4, u=1. Thus the unit gradient is [1,2,3],
while local saved X is [1,2,4] and source weight shards are [1,4]. Gradient
and weight values vary with position and rank; saved-X values are 11,13,17,
all different from global saved X=19. No output relation is assumed.
-/

namespace TrainVerify.Denote.DxUnitWitness
noncomputable section

-- Different DP units as well as different TP channels and sequence positions.
def G : Tensor := Tensor.mkShape [2, 2, 3]
  (fun j => ((1 + j.val : Nat) : Scalar))
def gradient (base : Nat) : Tensor := Tensor.mkShape [1, 2, 1]
  (fun j => ((base + 3 * j.val : Nat) : Scalar))
def gs : List Tensor := [gradient 7, gradient 8, gradient 9]
def weight (base : Nat) : Tensor := Tensor.mkShape [1, 4]
  (fun j => ((base + j.val : Nat) : Scalar))
def ws : List Tensor := [weight 1, weight 11, weight 21]
def W : Tensor := allGatherPrimDimN 0 3 0 ws
def saved (value : Scalar) : Tensor := Tensor.mkShape [1, 2, 4] (fun _ => value)
def xs : List Tensor := [saved 11, saved 13, saved 17]
def X : Tensor := Tensor.mkShape [2, 2, 4] (fun _ => 19)

/-- Exactly the adapter's tensor input contract at the concrete dimensions.
There are no output fields and no activation-value equalities. -/
structure InputContract (fullG fullX fullW : Tensor)
    (localGs localXs localWs : List Tensor) : Prop where
  gradient_shape : fullG.shape = [1 * 2, 2, 1 * 3]
  activation_shape : fullX.shape = [1 * 2, 2, 4]
  weight_shape : fullW.shape = [1 * 3, 4]
  gradient_length : localGs.length = 3
  activation_length : localXs.length = 3
  weight_length : localWs.length = 3
  gradient_shapes : ∀ g ∈ localGs, g.shape = [1, 2, 1]
  activation_shapes : ∀ x ∈ localXs, x.shape = [1, 2, 4]
  weight_shapes : ∀ w ∈ localWs, w.shape = [1, 4]
  gradient_value : chunkPrimDimN 0 2 1 fullG = allGatherPrimDimN 2 3 0 localGs
  weight_value : fullW = allGatherPrimDimN 0 3 0 localWs

theorem gradient_reconstruction :
    chunkPrimDimN 0 2 1 G = allGatherPrimDimN 2 3 0 gs := by
  refine Tensor.ext (t1 := chunkPrimDimN 0 2 1 G)
    (t2 := allGatherPrimDimN 2 3 0 gs) rfl ?_
  intro idx hidx
  change idx < 6 at hidx
  interval_cases idx <;> rfl

theorem input_contract : InputContract G X W gs xs ws := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_,
    gradient_reconstruction, rfl⟩
  · intro g hg
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> rfl
  · intro x hx
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rfl
  · intro w hw
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> rfl

/-- Each local saved X differs in value from the selected global DP chunk. -/
theorem independent_saved_values :
    ∀ x ∈ xs, valAt x 0 ≠ valAt (chunkPrimDimN 0 2 1 X) 0 := by
  intro x hx
  simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · change (11 : Scalar) ≠ 19
    norm_num
  · change (13 : Scalar) ≠ 19
    norm_num
  · change (17 : Scalar) ≠ 19
    norm_num

/-- Saved values also differ between all three TP ranks. -/
theorem pairwise_saved_values :
    valAt (xs.getD 0 (zeroTensor [])) 0 ≠ valAt (xs.getD 1 (zeroTensor [])) 0 ∧
    valAt (xs.getD 0 (zeroTensor [])) 0 ≠ valAt (xs.getD 2 (zeroTensor [])) 0 ∧
    valAt (xs.getD 1 (zeroTensor [])) 0 ≠ valAt (xs.getD 2 (zeroTensor [])) 0 := by
  change (11 : Scalar) ≠ 13 ∧ (11 : Scalar) ≠ 17 ∧ (13 : Scalar) ≠ 17
  norm_num

/-- The wrong DP unit is observably different, despite identical shapes. -/
theorem wrong_dp_unit : chunkPrimDimN 0 2 0 G ≠ allGatherPrimDimN 2 3 0 gs := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  change ((1 : Nat) : Scalar) = ((7 : Nat) : Scalar) at hv
  norm_num at hv

/-- Satisfiability is proved before applying any dX result. -/
theorem inputs_satisfiable :
    ∃ fullG fullX fullW : Tensor, ∃ localGs localXs localWs : List Tensor,
      InputContract fullG fullX fullW localGs localXs localWs ∧
      (∀ x ∈ localXs, valAt x 0 ≠ valAt (chunkPrimDimN 0 2 1 fullX) 0) ∧
      (valAt (localXs.getD 0 (zeroTensor [])) 0 ≠
        valAt (localXs.getD 1 (zeroTensor [])) 0 ∧
       valAt (localXs.getD 0 (zeroTensor [])) 0 ≠
        valAt (localXs.getD 2 (zeroTensor [])) 0 ∧
       valAt (localXs.getD 1 (zeroTensor [])) 0 ≠
        valAt (localXs.getD 2 (zeroTensor [])) 0) :=
  ⟨G, X, W, gs, xs, ws, input_contract, independent_saved_values, pairwise_saved_values⟩

/-- The adapter derives the output equality from the concrete input witness. -/
theorem adapter_result :
    chunkPrimDimN 0 2 1 (bw_linear G X W).1 =
      tensorSum (List.zipWith (fun (ga : Tensor × Tensor) (w : Tensor) => (bw_linear ga.1 ga.2 w).1)
        (List.zipWith Prod.mk gs xs) ws) := by
  exact source_bw_linear_dx_batch_tp_unit 2 3 1 2 1 4 1 G X W gs xs ws
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    input_contract.gradient_shape input_contract.activation_shape input_contract.weight_shape
    input_contract.gradient_length input_contract.activation_length input_contract.weight_length
    input_contract.gradient_shapes input_contract.activation_shapes input_contract.weight_shapes
    input_contract.gradient_value input_contract.weight_value

theorem no_rank_truncation :
    (List.zipWith (fun (ga : Tensor × Tensor) (w : Tensor) => (bw_linear ga.1 ga.2 w).1)
      (List.zipWith Prod.mk gs xs) ws).length = 3 :=
  source_bw_linear_dx_local_list_length 3 gs xs ws rfl rfl rfl

#print axioms wrong_dp_unit
#print axioms input_contract
#print axioms inputs_satisfiable
#print axioms independent_saved_values
#print axioms pairwise_saved_values
#print axioms adapter_result
#print axioms no_rank_truncation

end
end TrainVerify.Denote.DxUnitWitness
