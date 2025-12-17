import Mathlib.Data.Vector.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh -- For Real.arsinh
import Mathlib.Data.Real.Archimedean -- For floor, ceil
import Mathlib.Algebra.Order.Round -- For round
import Mathlib.Data.Real.Sign -- For Real.sign
import Mathlib.Analysis.SpecialFunctions.ExpDeriv -- For Real.exp, Real.log
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- For Real.sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic -- For Real.sin, Real.cos, Real.tan
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import trainverify.SIMDDefinition

namespace UnaryElementwiseOperators

open MeasureTheory Real

open SIMD

/-- Identity kernel function: 恒等函数 -/
def identityKernel : KernelFunction 1 :=
  fun v => v.get ⟨0, by norm_num⟩

/-- Abs kernel function: 绝对值函数 -/
noncomputable def absKernel : KernelFunction 1 :=
  fun v => abs (v.get ⟨0, by norm_num⟩)

/-- Neg kernel function: 取负函数 -/
def negKernel : KernelFunction 1 :=
  fun v => -(v.get ⟨0, by norm_num⟩)

/-- Not kernel function: 逻辑非函数 (非零值视为true) -/
noncomputable def notKernel : KernelFunction 1 :=
  fun v => if v.get ⟨0, by norm_num⟩ = 0 then 1 else 0

/-- Ceil kernel function: 向上取整函数 -/
noncomputable def ceilKernel : KernelFunction 1 :=
  fun v => ⌈v.get ⟨0, by norm_num⟩⌉

/-- Floor kernel function: 向下取整函数 -/
noncomputable def floorKernel : KernelFunction 1 :=
  fun v => ⌊v.get ⟨0, by norm_num⟩⌋

/-- Round kernel function: 四舍五入函数 -/
noncomputable def roundKernel : KernelFunction 1 :=
  fun v => round (v.get ⟨0, by norm_num⟩)

/-- Sign kernel function: 符号函数 -/
noncomputable def signKernel : KernelFunction 1 :=
  fun v => Real.sign (v.get ⟨0, by norm_num⟩)

/-- Reciprocal kernel function: 倒数函数 -/
noncomputable def reciprocalKernel : KernelFunction 1 :=
  fun v => 1 / (v.get ⟨0, by norm_num⟩)

/-- Exp kernel function: 指数函数 -/
noncomputable def expKernel : KernelFunction 1 :=
  fun v => Real.exp (v.get ⟨0, by norm_num⟩)

/-- Log kernel function: 自然对数函数 -/
noncomputable def logKernel : KernelFunction 1 :=
  fun v => Real.log (v.get ⟨0, by norm_num⟩)

/-- Sqrt kernel function: 平方根函数 -/
noncomputable def sqrtKernel : KernelFunction 1 :=
  fun v => Real.sqrt (v.get ⟨0, by norm_num⟩)

/-- Sin kernel function: 正弦函数 -/
noncomputable def sinKernel : KernelFunction 1 :=
  fun v => Real.sin (v.get ⟨0, by norm_num⟩)

/-- Cos kernel function: 余弦函数 -/
noncomputable def cosKernel : KernelFunction 1 :=
  fun v => Real.cos (v.get ⟨0, by norm_num⟩)

/-- Tan kernel function: 正切函数 -/
noncomputable def tanKernel : KernelFunction 1 :=
  fun v => Real.tan (v.get ⟨0, by norm_num⟩)

/-- Error function defined as erf(x) = (2/√π) ∫₀ˣ exp(-t²) dt -/
noncomputable def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt π) * ∫ t in (0)..(x), Real.exp (-(t ^ 2))

/-- Erf kernel function: 误差函数 -/
noncomputable def erfKernel : KernelFunction 1 :=
  fun v => erf (v.get ⟨0, by norm_num⟩)

-- ===== SIMD函数定义 =====

/-- Identity SIMD function -/
noncomputable def identitySIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims identityKernel

/-- Abs SIMD function -/
noncomputable def absSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims absKernel

/-- Neg SIMD function -/
noncomputable def negSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims negKernel

/-- Not SIMD function -/
noncomputable def notSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims notKernel

/-- Ceil SIMD function -/
noncomputable def ceilSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims ceilKernel

/-- Floor SIMD function -/
noncomputable def floorSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims floorKernel

/-- Round SIMD function -/
noncomputable def roundSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims roundKernel

/-- Sign SIMD function -/
noncomputable def signSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims signKernel

/-- Reciprocal SIMD function -/
noncomputable def reciprocalSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims reciprocalKernel

/-- Exp SIMD function -/
noncomputable def expSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims expKernel

/-- Log SIMD function -/
noncomputable def logSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims logKernel

/-- Sqrt SIMD function -/
noncomputable def sqrtSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims sqrtKernel

/-- Sin SIMD function -/
noncomputable def sinSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims sinKernel

/-- Cos SIMD function -/
noncomputable def cosSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims cosKernel

/-- Tan SIMD function -/
noncomputable def tanSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims tanKernel

/-- Erf SIMD function -/
noncomputable def erfSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims erfKernel

-- ===== SIMD性质证明 =====

/-- Proof that Identity is a SIMD function -/
theorem identity_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (identitySIMD dims input h_input_count h_dims)) := by
  simp only [identitySIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims identityKernel

/-- Proof that Abs is a SIMD function -/
theorem abs_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (absSIMD dims input h_input_count h_dims)) := by
  simp only [absSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims absKernel

/-- Proof that Neg is a SIMD function -/
theorem neg_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (negSIMD dims input h_input_count h_dims)) := by
  simp only [negSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims negKernel

/-- Proof that Not is a SIMD function -/
theorem not_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (notSIMD dims input h_input_count h_dims)) := by
  simp only [notSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims notKernel

/-- Proof that Ceil is a SIMD function -/
theorem ceil_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (ceilSIMD dims input h_input_count h_dims)) := by
  simp only [ceilSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims ceilKernel

/-- Proof that Floor is a SIMD function -/
theorem floor_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (floorSIMD dims input h_input_count h_dims)) := by
  simp only [floorSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims floorKernel

/-- Proof that Round is a SIMD function -/
theorem round_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (roundSIMD dims input h_input_count h_dims)) := by
  simp only [roundSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims roundKernel

/-- Proof that Sign is a SIMD function -/
theorem sign_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (signSIMD dims input h_input_count h_dims)) := by
  simp only [signSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims signKernel

/-- Proof that Reciprocal is a SIMD function -/
theorem reciprocal_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (reciprocalSIMD dims input h_input_count h_dims)) := by
  simp only [reciprocalSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims reciprocalKernel

/-- Proof that Exp is a SIMD function -/
theorem exp_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (expSIMD dims input h_input_count h_dims)) := by
  simp only [expSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims expKernel

/-- Proof that Log is a SIMD function -/
theorem log_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (logSIMD dims input h_input_count h_dims)) := by
  simp only [logSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims logKernel

/-- Proof that Sqrt is a SIMD function -/
theorem sqrt_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (sqrtSIMD dims input h_input_count h_dims)) := by
  simp only [sqrtSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims sqrtKernel

/-- Proof that Sin is a SIMD function -/
theorem sin_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (sinSIMD dims input h_input_count h_dims)) := by
  simp only [sinSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims sinKernel

/-- Proof that Cos is a SIMD function -/
theorem cos_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (cosSIMD dims input h_input_count h_dims)) := by
  simp only [cosSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims cosKernel

/-- Proof that Tan is a SIMD function -/
theorem tan_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (tanSIMD dims input h_input_count h_dims)) := by
  simp only [tanSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims tanKernel

/-- Proof that Erf is a SIMD function -/
theorem erf_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (erfSIMD dims input h_input_count h_dims)) := by
  simp only [erfSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims erfKernel

-- ===== Kernel良构性证明 =====

/-- Theorem: Identity kernel function is well-formed -/
theorem identity_is_wellformed : WellFormedKernel 1 identityKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1 as different input values
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j (vacuously true)
      intro j hj
      fin_cases j
      contradiction
    · -- 3. identityKernel v ≠ identityKernel v'
      simp only [identityKernel, List.Vector.get_ofFn]
      norm_num

/-- Theorem: Abs kernel function is well-formed -/
theorem abs_is_wellformed : WellFormedKernel 1 absKernel := by
  intro i
  fin_cases i
  -- Use -1 and 1 as input values: abs(-1) = 1, abs(1) = 1, but the function still distinguishes inputs
  -- Better: use 0 and 1: abs(0) = 0, abs(1) = 1
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. absKernel v ≠ absKernel v'
      simp only [absKernel, List.Vector.get_ofFn]
      simp [abs_zero, abs_one]

/-- Theorem: Neg kernel function is well-formed -/
theorem neg_is_wellformed : WellFormedKernel 1 negKernel := by
  intro i
  fin_cases i
  -- Use 1 and 2: neg(1) = -1, neg(2) = -2
  use List.Vector.ofFn (fun _ => (1 : ℝ)), List.Vector.ofFn (fun _ => (2 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. negKernel v ≠ negKernel v'
      simp only [negKernel, List.Vector.get_ofFn]
      norm_num

/-- Theorem: Not kernel function is well-formed -/
theorem not_is_wellformed : WellFormedKernel 1 notKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1: not(0) = 1, not(1) = 0
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. notKernel v ≠ notKernel v'
      simp only [notKernel, List.Vector.get_ofFn]
      simp [if_pos, if_neg]

/-- Theorem: Ceil kernel function is well-formed -/
theorem ceil_is_wellformed : WellFormedKernel 1 ceilKernel := by
  intro i
  fin_cases i
  -- Use 0.5 and 1.5: ceil(0.5) = 1, ceil(1.5) = 2
  use List.Vector.ofFn (fun _ => (0.5 : ℝ)), List.Vector.ofFn (fun _ => (1.5 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
    norm_num
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. ceilKernel v ≠ ceilKernel v'
      simp only [ceilKernel, List.Vector.get_ofFn]
      -- Goal: ⌈0.5⌉ ≠ ⌈1.5⌉, i.e., 1 ≠ 2
      norm_cast
      norm_num

/-- Theorem: Floor kernel function is well-formed -/
theorem floor_is_wellformed : WellFormedKernel 1 floorKernel := by
  intro i
  fin_cases i
  -- Use 0.5 and 1.5: floor(0.5) = 0, floor(1.5) = 1
  use List.Vector.ofFn (fun _ => (0.5 : ℝ)), List.Vector.ofFn (fun _ => (1.5 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
    norm_num
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. floorKernel v ≠ floorKernel v'
      simp only [floorKernel, List.Vector.get_ofFn]
      -- Goal: ⌊0.5⌋ ≠ ⌊1.5⌋, i.e., 0 ≠ 1
      norm_cast
      norm_num

/-- Theorem: Round kernel function is well-formed -/
theorem round_is_wellformed : WellFormedKernel 1 roundKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1: round(0) = 0, round(1) = 1
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. roundKernel v ≠ roundKernel v'
      simp only [roundKernel, List.Vector.get_ofFn]
      -- Goal: round(0) ≠ round(1), i.e., 0 ≠ 1
      rw [round_zero, round_one]
      norm_cast

/-- Theorem: Sign kernel function is well-formed -/
theorem sign_is_wellformed : WellFormedKernel 1 signKernel := by
  intro i
  fin_cases i
  -- Use -1 and 1: sign(-1) = -1, sign(1) = 1
  use List.Vector.ofFn (fun _ => (-1 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
    norm_num
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. signKernel v ≠ signKernel v'
      simp only [signKernel, List.Vector.get_ofFn]
      -- Goal: Real.sign(-1) ≠ Real.sign(1), i.e., -1 ≠ 1
      rw [Real.sign_of_neg (by norm_num : (-1 : ℝ) < 0)]
      rw [Real.sign_of_pos (by norm_num : (0 : ℝ) < 1)]
      norm_num

/-- Theorem: Reciprocal kernel function is well-formed -/
theorem reciprocal_is_wellformed : WellFormedKernel 1 reciprocalKernel := by
  intro i
  fin_cases i
  -- Use 1 and 2: reciprocal(1) = 1, reciprocal(2) = 0.5
  use List.Vector.ofFn (fun _ => (1 : ℝ)), List.Vector.ofFn (fun _ => (2 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. reciprocalKernel v ≠ reciprocalKernel v'
      simp only [reciprocalKernel, List.Vector.get_ofFn]
      -- Goal: 1/1 ≠ 1/2, i.e., 1 ≠ 0.5
      norm_num

/-- Theorem: Exp kernel function is well-formed -/
theorem exp_is_wellformed : WellFormedKernel 1 expKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1: exp(0) = 1, exp(1) = e
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. expKernel v ≠ expKernel v'
      simp only [expKernel, List.Vector.get_ofFn]
      -- Goal: exp(0) ≠ exp(1), i.e., 1 ≠ e
      rw [Real.exp_zero]
      have h_exp_one_ne_one : Real.exp 1 ≠ 1 := by
        have h : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
        exact ne_of_gt h
      exact h_exp_one_ne_one.symm

/-- Theorem: Log kernel function is well-formed -/
theorem log_is_wellformed : WellFormedKernel 1 logKernel := by
  intro i
  fin_cases i
  -- Use 1 and e: log(1) = 0, log(e) = 1
  use List.Vector.ofFn (fun _ => (1 : ℝ)), List.Vector.ofFn (fun _ => Real.exp 1)
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
    have h : (1 : ℝ) ≠ Real.exp 1 := by
      have h_gt : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      exact ne_of_lt h_gt
    exact h
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. logKernel v ≠ logKernel v'
      simp only [logKernel, List.Vector.get_ofFn]
      -- Goal: log(1) ≠ log(e), i.e., 0 ≠ 1
      rw [Real.log_one]
      have h_log_exp : Real.log (Real.exp 1) = 1 := by
        rw [Real.log_exp]
      rw [h_log_exp]
      norm_num

/-- Theorem: Sqrt kernel function is well-formed -/
theorem sqrt_is_wellformed : WellFormedKernel 1 sqrtKernel := by
  intro i
  fin_cases i
  -- Use 1 and 4: sqrt(1) = 1, sqrt(4) = 2
  use List.Vector.ofFn (fun _ => (1 : ℝ)), List.Vector.ofFn (fun _ => (4 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. sqrtKernel v ≠ sqrtKernel v'
      simp only [sqrtKernel, List.Vector.get_ofFn]
      -- Goal: sqrt(1) ≠ sqrt(4), i.e., 1 ≠ 2
      rw [Real.sqrt_one]
      have h_sqrt_four : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq]
        · norm_num
        · norm_num
        · norm_num
      rw [h_sqrt_four]
      norm_num

/-- Theorem: Sin kernel function is well-formed -/
theorem sin_is_wellformed : WellFormedKernel 1 sinKernel := by
  intro i
  fin_cases i
  -- Use 0 and π/2: sin(0) = 0, sin(π/2) = 1
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => Real.pi / 2)
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
    have h : (0 : ℝ) ≠ Real.pi / 2 := by
      have h_pos : 0 < Real.pi / 2 := by
        rw [div_pos_iff]
        left
        exact ⟨Real.pi_pos, by norm_num⟩
      exact ne_of_lt h_pos
    exact h
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. sinKernel v ≠ sinKernel v'
      simp only [sinKernel, List.Vector.get_ofFn]
      -- Goal: sin(0) ≠ sin(π/2), i.e., 0 ≠ 1
      rw [Real.sin_zero, Real.sin_pi_div_two]
      norm_num

/-- Theorem: Cos kernel function is well-formed -/
theorem cos_is_wellformed : WellFormedKernel 1 cosKernel := by
  intro i
  fin_cases i
  -- Use 0 and π/2: cos(0) = 1, cos(π/2) = 0
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => Real.pi / 2)
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
    have h : (0 : ℝ) ≠ Real.pi / 2 := by
      have h_pos : 0 < Real.pi / 2 := by
        rw [div_pos_iff]
        left
        exact ⟨Real.pi_pos, by norm_num⟩
      exact ne_of_lt h_pos
    exact h
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. cosKernel v ≠ cosKernel v'
      simp only [cosKernel, List.Vector.get_ofFn]
      -- Goal: cos(0) ≠ cos(π/2), i.e., 1 ≠ 0
      rw [Real.cos_zero, Real.cos_pi_div_two]
      norm_num

/-- Theorem: Tan kernel function is well-formed -/
theorem tan_is_wellformed : WellFormedKernel 1 tanKernel := by
  intro i
  fin_cases i
  -- Use 0 and π/4: tan(0) = 0, tan(π/4) = 1
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => Real.pi / 4)
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
    have h : (0 : ℝ) ≠ Real.pi / 4 := by
      have h_pos : 0 < Real.pi / 4 := by
        rw [div_pos_iff]
        left
        exact ⟨Real.pi_pos, by norm_num⟩
      exact ne_of_lt h_pos
    exact h
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. tanKernel v ≠ tanKernel v'
      simp only [tanKernel, List.Vector.get_ofFn]
      -- Goal: tan(0) ≠ tan(π/4), i.e., 0 ≠ 1
      rw [Real.tan_zero, Real.tan_pi_div_four]
      norm_num

theorem erf_is_wellformed : WellFormedKernel 1 erfKernel := by
  intro i
  fin_cases i
  -- Use 0 and 1: erf is strictly increasing, so erf(0) ≠ erf(1)
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      fin_cases j
      contradiction
    · -- 3. erfKernel v ≠ erfKernel v'
      simp only [erfKernel, List.Vector.get_ofFn, erf]
      -- erf(0) = (2/√π) * ∫₀⁰ e^(-t²) dt = 0
      -- erf(1) = (2/√π) * ∫₀¹ e^(-t²) dt > 0
      -- Therefore erf(0) ≠ erf(1)
      rw [intervalIntegral.integral_same, mul_zero]
      -- Now we need to show 0 ≠ (2/√π) * ∫₀¹ e^(-t²) dt
      apply ne_of_lt
      -- Show 0 < erf(1)
      apply mul_pos
      · -- 2/√π > 0
        apply div_pos
        · norm_num
        · exact Real.sqrt_pos.mpr Real.pi_pos
      · -- ∫₀¹ e^(-t²) dt > 0
        -- This follows from the fundamental theorem: if f is continuous and positive
        -- on [a,b] with a < b, then ∫ₐᵇ f(x) dx > 0
        -- Since exp(-t²) > 0 for all t and we integrate over [0,1], the result is positive
        apply intervalIntegral.intervalIntegral_pos_of_pos
        · -- The function is integrable
          apply ContinuousOn.intervalIntegrable
          exact (continuous_exp.comp (continuous_neg.comp (continuous_pow 2))).continuousOn
        · -- The function is positive everywhere
          intro t
          exact Real.exp_pos _
        · -- 0 < 1
          norm_num

/-- Asinh kernel function: applies inverse hyperbolic sine to a single input -/
noncomputable def asinhKernel : KernelFunction 1 :=
  fun v => Real.arsinh (v.get ⟨0, by norm_num⟩)

/-- Asinh SIMD function (使用通用的element-wise构造器) -/
noncomputable def asinhSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    SIMDFunction input dims :=
  createUnaryElementwiseSIMD dims input h_input_count h_dims asinhKernel

/-- Proof that Asinh is a SIMD function (使用通用的element-wise证明模板) -/
theorem asinh_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 1)
    (h_dims : input.dims.get ⟨0, by rw [h_input_count]; norm_num⟩ = dims) :
    isSIMDFunction input dims (fun _ => applySIMD input dims (asinhSIMD dims input h_input_count h_dims)) := by
  -- asinhSIMD 被定义为 createUnaryElementwiseSIMD，所以我们使用通用的证明
  simp only [asinhSIMD]
  exact unaryElementwise_is_SIMD dims input h_input_count h_dims asinhKernel

/-- Theorem: Asinh kernel function is well-formed -/
theorem asinh_is_wellformed : WellFormedKernel 1 asinhKernel := by
  intro i
  -- Since k = 1, we have i = 0
  fin_cases i
  -- Construct two vectors: v with value 0, v' with value 1
  use List.Vector.ofFn (fun _ => (0 : ℝ)), List.Vector.ofFn (fun _ => (1 : ℝ))
  constructor
  · -- 1. v.get 0 ≠ v'.get 0
    simp [List.Vector.get_ofFn]
  · constructor
    · -- 2. ∀ j : Fin 1, j ≠ 0 → v.get j = v'.get j
      intro j hj
      -- This is vacuously true since there's no j ≠ 0 in Fin 1
      fin_cases j
      contradiction
    · -- 3. asinhKernel v ≠ asinhKernel v'
      simp only [asinhKernel, List.Vector.get_ofFn]
      -- Goal: Real.arsinh 0 ≠ Real.arsinh 1
      -- We know arsinh is strictly monotonic and injective
      have h_inj := StrictMono.injective Real.arsinh_strictMono
      have h_ne : (0 : ℝ) ≠ 1 := by norm_num
      exact h_inj.ne h_ne

end UnaryElementwiseOperators
