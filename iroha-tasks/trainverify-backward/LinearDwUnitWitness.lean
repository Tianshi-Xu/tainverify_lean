import denote.SourceBWLinearDwUnit

/-!
Edit-only nondegenerate dW witness: K=3, B=2, S=3, I=4, O=5.
Full G and X are independent explicit flat tensors, not aliases for gathers.
Both their local values and their rank offsets vary. The input contract has
no output field. Parent must compile and inspect all printed axiom receipts.
-/

namespace TrainVerify.Denote.LinearDwUnitWitness
noncomputable section
set_option maxHeartbeats 500000

def G : Tensor := Tensor.mkShape [6,3,5] (fun j => ((1 + j.val : Nat) : Scalar))
def X : Tensor := Tensor.mkShape [6,3,4] (fun j => ((2 + 2*j.val : Nat) : Scalar))
def W : Tensor := Tensor.mkShape [5,4] (fun j => ((7 + j.val : Nat) : Scalar))
def gradient (r : Nat) : Tensor :=
  Tensor.mkShape [2,3,5] (fun j => ((1 + 30*r + j.val : Nat) : Scalar))
def saved (r : Nat) : Tensor :=
  Tensor.mkShape [2,3,4] (fun j => ((2 + 48*r + 2*j.val : Nat) : Scalar))
def gs : List Tensor := [gradient 0, gradient 1, gradient 2]
def xs : List Tensor := [saved 0, saved 1, saved 2]

structure InputContract (g x w : Tensor) (gs xs : List Tensor) : Prop where
  gradient_shape : g.shape = [2*3,3,5]
  activation_shape : x.shape = [2*3,3,4]
  weight_shape : w.shape = [5,4]
  gradient_length : gs.length = 3
  activation_length : xs.length = 3
  gradient_shapes : ∀ g ∈ gs, g.shape = [2,3,5]
  activation_shapes : ∀ x ∈ xs, x.shape = [2,3,4]
  gradient_value : g = allGatherPrimDimN 0 3 0 gs
  activation_value : x = allGatherPrimDimN 0 3 0 xs

theorem gradient_reconstruction : G = allGatherPrimDimN 0 3 0 gs := by
  refine Tensor.ext (t1 := G) (t2 := allGatherPrimDimN 0 3 0 gs) ?_ ?_
  · rfl
  · intro j hj
    change j < 90 at hj
    interval_cases j <;> rfl

theorem saved_reconstruction : X = allGatherPrimDimN 0 3 0 xs := by
  refine Tensor.ext (t1 := X) (t2 := allGatherPrimDimN 0 3 0 xs) ?_ ?_
  · rfl
  · intro j hj
    change j < 72 at hj
    interval_cases j <;> rfl

theorem input_contract : InputContract G X W gs xs := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_,
    gradient_reconstruction, saved_reconstruction⟩
  · intro g hg
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> rfl
  · intro x hx
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rfl

-- Raw values across ranks, before applying any dW theorem.
theorem rank_raw_values :
    valAt (gradient 0) 0 = 1 ∧ valAt (gradient 1) 0 = 31 ∧
    valAt (gradient 2) 0 = 61 ∧ valAt (saved 0) 0 = 2 ∧
    valAt (saved 1) 0 = 50 ∧ valAt (saved 2) 0 = 98 := by
  change ((1 : Nat) : Scalar) = 1 ∧ ((31 : Nat) : Scalar) = 31 ∧
    ((61 : Nat) : Scalar) = 61 ∧ ((2 : Nat) : Scalar) = 2 ∧
    ((50 : Nat) : Scalar) = 50 ∧ ((98 : Nat) : Scalar) = 98
  norm_num

theorem nonconstant_inputs :
    valAt G 0 ≠ valAt G 1 ∧ valAt X 0 ≠ valAt X 1 ∧
    (∀ r ∈ [0,1,2], valAt (gradient r) 0 ≠ valAt (gradient r) 1 ∧
      valAt (saved r) 0 ≠ valAt (saved r) 1) := by
  refine ⟨?_, ?_, ?_⟩
  · change ((1 : Nat) : Scalar) ≠ ((2 : Nat) : Scalar)
    norm_num
  · change ((2 : Nat) : Scalar) ≠ ((4 : Nat) : Scalar)
    norm_num
  · intro r _
    change ((1 + 30*r : Nat) : Scalar) ≠ ((1 + 30*r + 1 : Nat) : Scalar) ∧
      ((2 + 48*r : Nat) : Scalar) ≠ ((2 + 48*r + 2 : Nat) : Scalar)
    exact_mod_cast (show (1 + 30*r : Nat) ≠ 1 + 30*r + 1 ∧
      (2 + 48*r : Nat) ≠ 2 + 48*r + 2 from ⟨by omega, by omega⟩)

theorem distinct_rank_saved_values :
    valAt (saved 0) 0 ≠ valAt (saved 1) 0 ∧
    valAt (saved 0) 0 ≠ valAt (saved 2) 0 ∧
    valAt (saved 1) 0 ≠ valAt (saved 2) 0 := by
  change ((2 : Nat) : Scalar) ≠ ((50 : Nat) : Scalar) ∧
    ((2 : Nat) : Scalar) ≠ ((98 : Nat) : Scalar) ∧
    ((50 : Nat) : Scalar) ≠ ((98 : Nat) : Scalar)
  norm_num

-- Negative control: same shape but wrong saved values violate the contract.
theorem zero_saved_rejected :
    zeroTensor [6,3,4] ≠ allGatherPrimDimN 0 3 0 xs := by
  intro he
  have hv := congrArg (fun t => valAt t 0) he
  rw [← saved_reconstruction] at hv
  change (0 : Scalar) = ((2 : Nat) : Scalar) at hv
  norm_num at hv

theorem inputs_satisfiable :
    ∃ g x w : Tensor, ∃ gs xs : List Tensor,
      InputContract g x w gs xs ∧ valAt g 0 ≠ valAt g 1 ∧
      valAt x 0 ≠ valAt x 1 :=
  ⟨G, X, W, gs, xs, input_contract, nonconstant_inputs.1, nonconstant_inputs.2.1⟩

theorem adapter_result :
    (bw_linear G X W).2 =
      tensorSum (List.zipWith (fun g x => (bw_linear g x W).2) gs xs) := by
  exact source_bw_linear_dw_batch_unit 3 2 3 5 4 G X W gs xs
    (by decide) (by decide) (by decide) (by decide) (by decide)
    input_contract.gradient_shape input_contract.activation_shape input_contract.weight_shape
    input_contract.gradient_length input_contract.activation_length
    input_contract.gradient_shapes input_contract.activation_shapes
    input_contract.gradient_value input_contract.activation_value

theorem output_shapes :
    (bw_linear G X W).2.shape = [5,4] ∧
    (tensorSum (List.zipWith (fun g x => (bw_linear g x W).2) gs xs)).shape = [5,4] := by
  have h := bw_linear_3d_snd_shape 6 3 5 4 G X W rfl rfl rfl
  refine ⟨h, ?_⟩
  rw [← adapter_result]
  exact h

theorem no_rank_truncation :
    (List.zipWith (fun g x => (bw_linear g x W).2) gs xs).length = 3 := rfl

#print axioms G
#print axioms X
#print axioms W
#print axioms gradient
#print axioms saved
#print axioms gs
#print axioms xs
#print axioms InputContract
#print axioms gradient_reconstruction
#print axioms saved_reconstruction
#print axioms input_contract
#print axioms rank_raw_values
#print axioms nonconstant_inputs
#print axioms distinct_rank_saved_values
#print axioms zero_saved_rejected
#print axioms inputs_satisfiable
#print axioms adapter_result
#print axioms output_shapes
#print axioms no_rank_truncation

end
end TrainVerify.Denote.LinearDwUnitWitness
