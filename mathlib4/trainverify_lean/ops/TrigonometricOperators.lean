import Mathlib.Data.Vector.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic -- For Real.sin, Real.cos, Real.tan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse -- For Real.arcsin, Real.arccos
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan -- For Real.arctan
import Mathlib.Data.Complex.Trigonometric -- For Real.sinh, Real.cosh, Real.tanh
import trainverify.SIMDDefinition

namespace TrigonometricOperators

open Real SIMD

-- ===== Kernel函数定义 =====

/-- Asin kernel function: 反正弦函数 -/
noncomputable def asinKernel : KernelFunction 1 :=
  fun v => arcsin (v.get ⟨0, by norm_num⟩)

/-- Acos kernel function: 反余弦函数 -/
noncomputable def acosKernel : KernelFunction 1 :=
  fun v => arccos (v.get ⟨0, by norm_num⟩)

/-- Atan kernel function: 反正切函数 -/
noncomputable def atanKernel : KernelFunction 1 :=
  fun v => arctan (v.get ⟨0, by norm_num⟩)

/-- Sinh kernel function: 双曲正弦函数 -/
noncomputable def sinhKernel : KernelFunction 1 :=
  fun v => sinh (v.get ⟨0, by norm_num⟩)

/-- Cosh kernel function: 双曲余弦函数 -/
noncomputable def coshKernel : KernelFunction 1 :=
  fun v => cosh (v.get ⟨0, by norm_num⟩)

/-- Tanh kernel function: 双曲正切函数 -/
noncomputable def tanhKernel : KernelFunction 1 :=
  fun v => tanh (v.get ⟨0, by norm_num⟩)

-- ===== SIMD函数定义 =====

/-- Asin SIMD function -/
noncomputable def asinSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims asinKernel

/-- Acos SIMD function -/
noncomputable def acosSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims acosKernel

/-- Atan SIMD function -/
noncomputable def atanSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims atanKernel

/-- Sinh SIMD function -/
noncomputable def sinhSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims sinhKernel

/-- Cosh SIMD function -/
noncomputable def coshSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims coshKernel

/-- Tanh SIMD function -/
noncomputable def tanhSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims tanhKernel

-- ===== SIMD性质证明 =====

/-- Proof that Asin is a SIMD function -/
theorem asin_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (asinSIMD dims input h_input_count h_dims)) := by
  simp only [asinSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims asinKernel

/-- Proof that Acos is a SIMD function -/
theorem acos_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (acosSIMD dims input h_input_count h_dims)) := by
  simp only [acosSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims acosKernel

/-- Proof that Atan is a SIMD function -/
theorem atan_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (atanSIMD dims input h_input_count h_dims)) := by
  simp only [atanSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims atanKernel

/-- Proof that Sinh is a SIMD function -/
theorem sinh_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (sinhSIMD dims input h_input_count h_dims)) := by
  simp only [sinhSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims sinhKernel

/-- Proof that Cosh is a SIMD function -/
theorem cosh_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (coshSIMD dims input h_input_count h_dims)) := by
  simp only [coshSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims coshKernel

/-- Proof that Tanh is a SIMD function -/
theorem tanh_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (tanhSIMD dims input h_input_count h_dims)) := by
  simp only [tanhSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims tanhKernel

-- ===== Kernel良构性证明 =====

/-- Theorem: Asin kernel function is well-formed -/
theorem asin_is_wellformed : WellFormedKernel 1 asinKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1/2: arcsin(0) = 0, arcsin(1/2) = π/6
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1/2 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. asinKernel v ≠ asinKernel v'
      simp only [asinKernel, List.Vector.get_ofFn]
      -- Goal: arcsin(0) ≠ arcsin(1/2)
      -- We know arcsin is injective and 0 ≠ 1/2
      have h_ne : (0 : ℝ) ≠ (1/2) := by norm_num
      -- Now use that arcsin is a function
      intro h_eq
      -- From arcsin(0) = arcsin(1/2), we get 0 = 1/2 which contradicts h_ne
      rw [arcsin_zero] at h_eq
      have h_pos : (0 : ℝ) < arcsin (1/2) := by
        rw [arcsin_pos]
        norm_num
      linarith

/-- Theorem: Acos kernel function is well-formed -/
theorem acos_is_wellformed : WellFormedKernel 1 acosKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1: arccos(0) = π/2, arccos(1) = 0
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. acosKernel v ≠ acosKernel v'
      simp only [acosKernel, List.Vector.get_ofFn]
      -- Goal: arccos(0) ≠ arccos(1)
      -- Since arccos is strictly anti-monotonic, and 0 < 1, we have arccos(0) > arccos(1)
      apply ne_of_gt
      apply strictAntiOn_arccos
      · simp
      · simp
      · norm_num

/-- Theorem: Atan kernel function is well-formed -/
theorem atan_is_wellformed : WellFormedKernel 1 atanKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1: arctan(0) = 0, arctan(1) = π/4
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. atanKernel v ≠ atanKernel v'
      simp only [atanKernel, List.Vector.get_ofFn]
      -- Goal: arctan(0) ≠ arctan(1)
      -- We know arctan is strictly monotonic and injective
      have h_inj := StrictMono.injective arctan_strictMono
      have h_ne : (0 : ℝ) ≠ 1 := by norm_num
      exact h_inj.ne h_ne

/-- Theorem: Sinh kernel function is well-formed -/
theorem sinh_is_wellformed : WellFormedKernel 1 sinhKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1: sinh(0) = 0, sinh(1) = (e - e^(-1))/2
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. sinhKernel v ≠ sinhKernel v'
      simp only [sinhKernel, List.Vector.get_ofFn]
      -- Goal: sinh(0) ≠ sinh(1)
      -- sinh(0) = 0, sinh(1) > 0
      rw [sinh_zero]
      apply ne_of_lt
      apply sinh_pos_iff.mpr
      norm_num

/-- Theorem: Cosh kernel function is well-formed -/
theorem cosh_is_wellformed : WellFormedKernel 1 coshKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1: cosh(0) = 1, cosh(1) = (e + e^(-1))/2
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. coshKernel v ≠ coshKernel v'
      simp only [coshKernel, List.Vector.get_ofFn]
      -- Goal: cosh(0) ≠ cosh(1)
      -- cosh(0) = 1, cosh(1) = (e + 1/e)/2 > 1
      rw [cosh_zero]
      -- Show 1 < cosh(1) using the fact that cosh is increasing for nonnegative x
      apply ne_of_lt
      -- Use the fact that cosh(x) > 1 when x ≠ 0
      have h_one_lt_cosh : 1 < cosh 1 := by
        rw [one_lt_cosh]
        norm_num
      exact h_one_lt_cosh

/-- Theorem: Tanh kernel function is well-formed -/
theorem tanh_is_wellformed : WellFormedKernel 1 tanhKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1: tanh(0) = 0, tanh(1) = (e^2 - 1)/(e^2 + 1)
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. tanhKernel v ≠ tanhKernel v'
      simp only [tanhKernel, List.Vector.get_ofFn]
      -- Goal: tanh(0) ≠ tanh(1)
      -- tanh(0) = 0, tanh(1) > 0 since sinh(1) > 0 and cosh(1) > 0
      rw [tanh_zero]
      apply ne_of_lt
      -- Show 0 < tanh(1) by using tanh(x) = sinh(x)/cosh(x) and properties of sinh/cosh
      rw [tanh_eq_sinh_div_cosh]
      apply div_pos
      · -- sinh(1) > 0
        apply sinh_pos_iff.mpr
        norm_num
      · -- cosh(1) > 0 (always positive)
        exact cosh_pos 1

end TrigonometricOperators
