import trainverify.SIMDDefinition

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SIMD

-- ================================================================================
-- Helper Lemmas
-- ================================================================================

/-- Helper lemma: valid output index gives valid component indices -/
lemma valid_output_components (M N : ℕ) (out_idx : Index 2)
    (h_valid : validIndex [M, N] out_idx) :
    out_idx.get ⟨0, by norm_num⟩ < M ∧ out_idx.get ⟨1, by norm_num⟩ < N := by
  simp [validIndex] at h_valid
  exact ⟨h_valid ⟨0, by norm_num⟩, h_valid ⟨1, by norm_num⟩⟩

/-- Matrix multiplication kernel function: computes dot product of two P-element vectors -/
def matMulKernel (P : ℕ) : KernelFunction (2 * P) :=
  fun v => ∑ k : Fin P, (v.get ⟨k.val, by
    have h : k.val < P := Fin.is_lt k
    linarith⟩) *
                        (v.get ⟨k.val + P, by
    have h : k.val < P := Fin.is_lt k
    linarith⟩)

/-- Matrix multiplication dependency mapping -/
def matMulDependency (M P N : ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims_A : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = [M, P])
    (h_dims_B : input.dims.get ⟨1, by rw [h_input_count]; norm_num⟩ = [P, N]) :
    GeneralizedDependencyMapping input [M, N] (2 * P) :=
{
  map := fun out_idx =>
    let i := out_idx.get ⟨0, by norm_num⟩
    let j := out_idx.get ⟨1, by norm_num⟩
    -- Create combined vector of 2*P pointers
    List.Vector.ofFn (fun idx : Fin (2 * P) =>
      if h : idx.val < P then
        -- First P elements: A[i, k] for k = 0..P-1
        { tensor_idx := ⟨0, by rw [h_input_count]; norm_num⟩,
          multi_dim_idx := ⟨[i, idx.val], by simp [h_dims_A]⟩ }
      else
        -- Next P elements: B[k, j] for k = 0..P-1
        { tensor_idx := ⟨1, by rw [h_input_count]; norm_num⟩,
          multi_dim_idx := ⟨[idx.val - P, j], by
            have h_ge : P ≤ idx.val := Nat.le_of_not_gt h
            simp [h_dims_B, Nat.sub_lt_iff_lt_add h_ge, Fin.is_lt]⟩ }),
  valid := by
    intro out_idx h_valid_out idx
    simp [List.Vector.get_ofFn]
    -- Split by whether idx.val < P or not
    split_ifs with h_lt
    case pos =>
      -- Case: idx.val < P, accessing A[i, k] where k = idx.val
      simp [validInputPointer, validIndex, h_dims_A]
      intro j
      -- Get components of out_idx
      obtain ⟨h_i_bound, h_j_bound⟩ := valid_output_components M N out_idx h_valid_out
      let k := idx.val
      have h_k_bound : k < P := h_lt
      -- For matrix A[M, P], j can only be 0 or 1
      have h_j_bound_2 : j.val < 2 := by
        convert j.isLt using 1
        simp [h_dims_A]
      have h_j_cases : j.val = 0 ∨ j.val = 1 := by omega
      cases h_j_cases with
      | inl h_j_0 =>
        -- j = 0: accessing row index
        simp [h_j_0, List.Vector.get, List.get]
        -- Use the fact that get 0 = head
        rw [← List.Vector.get_zero]
        exact h_i_bound
      | inr h_j_1 =>
        -- j = 1: accessing column index k
        simp [h_j_1, List.Vector.get, List.get]
        exact h_k_bound
    case neg =>
      -- Case: idx.val ≥ P, accessing B[k, j] where k = idx.val - P
      simp [validInputPointer, validIndex, h_dims_B]
      intro j
      -- Get components of out_idx
      obtain ⟨h_i_bound, h_j_bound⟩ := valid_output_components M N out_idx h_valid_out
      let k := idx.val - P
      have h_k_bound : k < P := by
        have h_idx_bound : idx.val < 2 * P := Fin.is_lt idx
        have h_ge : P ≤ idx.val := Nat.le_of_not_gt h_lt
        omega
      -- For matrix B[P, N], j can only be 0 or 1
      have h_j_bound_2 : j.val < 2 := by
        convert j.isLt using 1
        simp [h_dims_B]
      have h_j_cases : j.val = 0 ∨ j.val = 1 := by omega
      cases h_j_cases with
      | inl h_j_0 =>
        -- j = 0: accessing row index k
        simp [h_j_0, List.Vector.get, List.get]
        exact h_k_bound
      | inr h_j_1 =>
        -- j = 1: accessing column index from output
        simp [h_j_1, List.Vector.get, List.get]
        exact h_j_bound
}

/-- Matrix multiplication SIMD function -/
def matMulSIMD (M P N : ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims_A : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = [M, P])
    (h_dims_B : input.dims.get ⟨1, by rw [h_input_count]; norm_num⟩ = [P, N]) :
    SIMDFunction input [M, N] :=
{
  k := 2 * P,
  kernel := matMulKernel P,
  dependency := matMulDependency M P N input h_input_count h_dims_A h_dims_B
}

/-- ReLU kernel function: max(0, x) -/
def reluKernel : KernelFunction 1 :=
  fun v => max 0 (v.get ⟨0, by norm_num⟩)

/-- Theorem: ReLU is a well-formed kernel function -/
theorem relu_is_wellformed : WellFormedKernel 1 reluKernel := by
  intro i
  -- For k = 1, there's only one index i = 0
  have h_i_eq : i = 0 := by
    have : i.val < 1 := i.isLt
    interval_cases i.val
    ext; simp
  -- Construct two vectors: one with negative value, one with positive value
  use ⟨[-1], by norm_num⟩, ⟨[1], by norm_num⟩
  constructor
  · -- 1. v.get i ≠ v'.get i
    simp [h_i_eq, List.Vector.get]
    norm_num
  · constructor
    · -- 2. ∀ j : Fin k, j ≠ i → v.get j = v'.get j
      intro j hij
      -- Since k = 1, there are no other indices j ≠ i
      have h_j_eq : j = 0 := by
        have : j.val < 1 := j.isLt
        interval_cases j.val
        ext; simp
      rw [h_j_eq, h_i_eq] at hij
      exact absurd rfl hij
    · -- 3. reluKernel v ≠ reluKernel v'
      simp only [reluKernel, h_i_eq, List.Vector.get, List.get]
      -- max(0, -1) = 0, max(0, 1) = 1, so 0 ≠ 1
      norm_num [max_def]

lemma validIndex_cast {d1 d2 : List ℕ} (h_dims_eq : d1 = d2)
    (v : Index d1.length) :
    validIndex d1 v ↔ validIndex d2 (h_dims_eq.symm ▸ v) := by
  subst h_dims_eq
  simp

/-- ReLU dependency mapping -/
def reluDependency (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    GeneralizedDependencyMapping input dims 1 :=
{
  map := fun out_idx =>
    List.Vector.ofFn (fun _ : Fin 1 =>
      { tensor_idx := ⟨0, by rw [h_input_count]; norm_num⟩,
        multi_dim_idx := h_dims.symm ▸ out_idx }),
  valid := by
    intro out_idx h_valid_out
    intro i
    -- There's only one element in the vector (i = 0)
    simp [List.Vector.get_ofFn]
    -- Need to prove validInputPointer for the mapped pointer
    simp [validInputPointer, validIndex]
    -- The goal is: ∀ (j : Fin (input.dims.get ⟨0, _⟩).length), (h_dims.symm ▸ out_idx).get j < (input.dims.get ⟨0, _⟩).get j
    -- Use subst to substitute h_dims equation
    subst h_dims
    -- Now the cast becomes identity and should simplify
    simp
    exact h_valid_out
}


/-- ReLU SIMD function -/
def reluSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
{
  k := 1,
  kernel := reluKernel,
  dependency := reluDependency dims input h_input_count h_dims
}

-- ============================================================================
-- Proofs that these are SIMD functions
-- ============================================================================

/-- Proof that matrix multiplication is a SIMD function -/
theorem matMul_is_SIMD (M P N : ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims_A : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = [M, P])
    (h_dims_B : input.dims.get ⟨1, by rw [h_input_count]; norm_num⟩ = [P, N]) :
    isSIMDFunction input [M, N] (fun _ => applySIMD input [M, N] (matMulSIMD M P N input h_input_count h_dims_A h_dims_B)) := by
  use matMulSIMD M P N input h_input_count h_dims_A h_dims_B

/-- Proof that ReLU is a SIMD function -/
theorem relu_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (reluSIMD dims input h_input_count h_dims)) := by
  use reluSIMD dims input h_input_count h_dims

end SIMD
