import Mathlib.Data.Vector.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import trainverify.SIMDDefinition

namespace SIMD

-- ===== 多元Element-wise算子支持 =====

/-- 多元element-wise依赖映射：用于所有多元element-wise算子
    假设所有输入张量都有相同维度，将每个输出索引映射到所有输入张量中的相同索引位置 -/
def multiaryElementwiseDependency (dims : List ℕ) (input : MultiTensorInput) (k : ℕ)
    (h_input_count : input.p = k)
    (h_dims : ∀ i : Fin k, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    GeneralizedDependencyMapping input dims k :=
{
  map := fun out_idx =>
    List.Vector.ofFn (fun i : Fin k =>
      { tensor_idx := ⟨i, by rw [h_input_count]; exact i.isLt⟩,
        multi_dim_idx := (h_dims i).symm ▸ out_idx }),
  valid := by
    intro out_idx h_valid_out
    intro i
    simp [List.Vector.get_ofFn]
    simp [validInputPointer, validIndex]
    have h_eq := h_dims i
    subst h_eq
    simp
    exact h_valid_out
}

/-- 通用多元element-wise SIMD函数构造器 -/
noncomputable def createMultiaryElementwiseSIMD (dims : List ℕ) (input : MultiTensorInput) (k : ℕ)
    (h_input_count : input.p = k)
    (h_dims : ∀ i : Fin k, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims)
    (kernel : KernelFunction k) :
    SIMDFunction input dims :=
{
  k := k,
  kernel := kernel,
  dependency := multiaryElementwiseDependency dims input k h_input_count h_dims
}

/-- 通用多元element-wise SIMD函数证明模板 -/
theorem multiaryElementwise_is_SIMD (dims : List ℕ) (input : MultiTensorInput) (k : ℕ)
    (h_input_count : input.p = k)
    (h_dims : ∀ i : Fin k, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims)
    (kernel : KernelFunction k) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (createMultiaryElementwiseSIMD dims input k h_input_count h_dims kernel)) := by
  use createMultiaryElementwiseSIMD dims input k h_input_count h_dims kernel

-- ===== Sum算子的具体实现（支持任意个输入）=====

/--
 SIMD函数（使用SIMDDefinition中的sumKernel）-/
noncomputable def sumSIMD (dims : List ℕ) (input : MultiTensorInput) (k : ℕ)
    (h_input_count : input.p = k)
    (h_dims : ∀ i : Fin k, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createMultiaryElementwiseSIMD dims input k h_input_count h_dims (sumKernel k)

/-- 证明Sum是SIMD函数 -/
theorem sum_is_SIMD (dims : List ℕ) (input : MultiTensorInput) (k : ℕ)
    (h_input_count : input.p = k)
    (h_dims : ∀ i : Fin k, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (sumSIMD dims input k h_input_count h_dims)) := by
  simp only [sumSIMD]
  use createMultiaryElementwiseSIMD dims input k h_input_count h_dims (sumKernel k)

-- ===== 二元Element-wise算子支持 =====

/-- 二元element-wise依赖映射：专门用于二元element-wise算子
    将每个输出索引映射到两个输入张量中的相同索引位置 -/
def binaryElementwiseDependency (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    GeneralizedDependencyMapping input dims 2 :=
  multiaryElementwiseDependency dims input 2 h_input_count h_dims

/-- 通用二元element-wise SIMD函数构造器 -/
noncomputable def createBinaryElementwiseSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims)
    (kernel : KernelFunction 2) :
    SIMDFunction input dims :=
  createMultiaryElementwiseSIMD dims input 2 h_input_count h_dims kernel

/-- 通用二元element-wise SIMD函数证明模板 -/
theorem binaryElementwise_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims)
    (kernel : KernelFunction 2) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (createBinaryElementwiseSIMD dims input h_input_count h_dims kernel)) := by
  use createBinaryElementwiseSIMD dims input h_input_count h_dims kernel

-- ===== 二元算子的具体实现 =====

/-- Add kernel function: 将两个标量相加 -/
def addKernel : KernelFunction 2 :=
  fun v => v.get ⟨0, by norm_num⟩ + v.get ⟨1, by norm_num⟩

/-- Sub kernel function: 两个标量相减 -/
def subKernel : KernelFunction 2 :=
  fun v => v.get ⟨0, by norm_num⟩ - v.get ⟨1, by norm_num⟩

/-- Mul kernel function: 两个标量相乘 -/
def mulKernel : KernelFunction 2 :=
  fun v => v.get ⟨0, by norm_num⟩ * v.get ⟨1, by norm_num⟩

/-- Div kernel function: 两个标量相除 -/
noncomputable def divKernel : KernelFunction 2 :=
  fun v => v.get ⟨0, by norm_num⟩ / v.get ⟨1, by norm_num⟩

/-- Pow kernel function: 幂运算 (base^exponent) -/
noncomputable def powKernel : KernelFunction 2 :=
  fun v => (v.get ⟨0, by norm_num⟩) ^ (v.get ⟨1, by norm_num⟩)

-- ===== 比较和逻辑算子 =====

/-- And kernel function: 逻辑与 (用实数0/1表示false/true) -/
noncomputable def andKernel : KernelFunction 2 :=
  fun v => if (v.get ⟨0, by norm_num⟩ ≠ 0) ∧ (v.get ⟨1, by norm_num⟩ ≠ 0) then 1 else 0

/-- Or kernel function: 逻辑或 -/
noncomputable def orKernel : KernelFunction 2 :=
  fun v => if (v.get ⟨0, by norm_num⟩ ≠ 0) ∨ (v.get ⟨1, by norm_num⟩ ≠ 0) then 1 else 0

/-- Xor kernel function: 逻辑异或 -/
noncomputable def xorKernel : KernelFunction 2 :=
  fun v => if (v.get ⟨0, by norm_num⟩ ≠ 0) ≠ (v.get ⟨1, by norm_num⟩ ≠ 0) then 1 else 0

/-- Equal kernel function: 相等比较 -/
noncomputable def equalKernel : KernelFunction 2 :=
  fun v => if v.get ⟨0, by norm_num⟩ = v.get ⟨1, by norm_num⟩ then 1 else 0

/-- Greater kernel function: 大于比较 -/
noncomputable def greaterKernel : KernelFunction 2 :=
  fun v => if v.get ⟨0, by norm_num⟩ > v.get ⟨1, by norm_num⟩ then 1 else 0

/-- Less kernel function: 小于比较 -/
noncomputable def lessKernel : KernelFunction 2 :=
  fun v => if v.get ⟨0, by norm_num⟩ < v.get ⟨1, by norm_num⟩ then 1 else 0

/-- GreaterOrEqual kernel function: 大于等于比较 -/
noncomputable def greaterOrEqualKernel : KernelFunction 2 :=
  fun v => if v.get ⟨0, by norm_num⟩ ≥ v.get ⟨1, by norm_num⟩ then 1 else 0

/-- LessOrEqual kernel function: 小于等于比较 -/
noncomputable def lessOrEqualKernel : KernelFunction 2 :=
  fun v => if v.get ⟨0, by norm_num⟩ ≤ v.get ⟨1, by norm_num⟩ then 1 else 0

/-- Add SIMD函数 -/
noncomputable def addSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims addKernel

/-- Sub SIMD函数 -/
noncomputable def subSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims subKernel

/-- Mul SIMD函数 -/
noncomputable def mulSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims mulKernel

/-- Div SIMD函数 -/
noncomputable def divSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims divKernel

/-- Pow SIMD函数 -/
noncomputable def powSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims powKernel

-- ===== 比较和逻辑算子SIMD函数 =====

/-- And SIMD函数 -/
noncomputable def andSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims andKernel

/-- Or SIMD函数 -/
noncomputable def orSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims orKernel

/-- Xor SIMD函数 -/
noncomputable def xorSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims xorKernel

/-- Equal SIMD函数 -/
noncomputable def equalSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims equalKernel

/-- Greater SIMD函数 -/
noncomputable def greaterSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims greaterKernel

/-- Less SIMD函数 -/
noncomputable def lessSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims lessKernel

/-- GreaterOrEqual SIMD函数 -/
noncomputable def greaterOrEqualSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims greaterOrEqualKernel

/-- LessOrEqual SIMD函数 -/
noncomputable def lessOrEqualSIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createBinaryElementwiseSIMD dims input h_input_count h_dims lessOrEqualKernel

-- ===== SIMD性质证明 =====

/-- 证明Add是SIMD函数 -/
theorem add_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (addSIMD dims input h_input_count h_dims)) := by
  simp only [addSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims addKernel

/-- 证明Sub是SIMD函数 -/
theorem sub_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (subSIMD dims input h_input_count h_dims)) := by
  simp only [subSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims subKernel

/-- 证明Mul是SIMD函数 -/
theorem mul_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (mulSIMD dims input h_input_count h_dims)) := by
  simp only [mulSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims mulKernel

/-- 证明Div是SIMD函数 -/
theorem div_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (divSIMD dims input h_input_count h_dims)) := by
  simp only [divSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims divKernel

/-- 证明Pow是SIMD函数 -/
theorem pow_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (powSIMD dims input h_input_count h_dims)) := by
  simp only [powSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims powKernel

-- ===== 比较和逻辑算子SIMD性质证明 =====

/-- 证明And是SIMD函数 -/
theorem and_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (andSIMD dims input h_input_count h_dims)) := by
  simp only [andSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims andKernel

/-- 证明Or是SIMD函数 -/
theorem or_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (orSIMD dims input h_input_count h_dims)) := by
  simp only [orSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims orKernel

/-- 证明Xor是SIMD函数 -/
theorem xor_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (xorSIMD dims input h_input_count h_dims)) := by
  simp only [xorSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims xorKernel

/-- 证明Equal是SIMD函数 -/
theorem equal_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (equalSIMD dims input h_input_count h_dims)) := by
  simp only [equalSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims equalKernel

/-- 证明Greater是SIMD函数 -/
theorem greater_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (greaterSIMD dims input h_input_count h_dims)) := by
  simp only [greaterSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims greaterKernel

/-- 证明Less是SIMD函数 -/
theorem less_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (lessSIMD dims input h_input_count h_dims)) := by
  simp only [lessSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims lessKernel

/-- 证明GreaterOrEqual是SIMD函数 -/
theorem greaterOrEqual_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (greaterOrEqualSIMD dims input h_input_count h_dims)) := by
  simp only [greaterOrEqualSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims greaterOrEqualKernel

/-- 证明LessOrEqual是SIMD函数 -/
theorem lessOrEqual_is_SIMD (dims : List ℕ) (input : MultiTensorInput)
    (h_input_count : input.p = 2)
    (h_dims : ∀ i : Fin 2, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (lessOrEqualSIMD dims input h_input_count h_dims)) := by
  simp only [lessOrEqualSIMD]
  exact binaryElementwise_is_SIMD dims input h_input_count h_dims lessOrEqualKernel

-- ===== Kernel良构性证明 =====

/-- 证明Add kernel function是良构的 -/
theorem add_kernel_is_wellformed : WellFormedKernel 2 addKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (1 : ℝ))
    constructor
    · -- v.get 0 ≠ v'.get 0
      simp [List.Vector.get_ofFn]
    · constructor
      · -- 其他位置相同
        intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · -- addKernel v ≠ addKernel v'
        simp only [addKernel, List.Vector.get_ofFn]
        norm_num
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (1 : ℝ))
    constructor
    · -- v.get 1 ≠ v'.get 1
      simp [List.Vector.get_ofFn]
    · constructor
      · -- 其他位置相同
        intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · -- addKernel v ≠ addKernel v'
        simp only [addKernel, List.Vector.get_ofFn]
        norm_num

/-- 证明Sub kernel function是良构的 -/
theorem sub_kernel_is_wellformed : WellFormedKernel 2 subKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [subKernel, List.Vector.get_ofFn]
        norm_num
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [subKernel, List.Vector.get_ofFn]
        norm_num

/-- 证明Mul kernel function是良构的 -/
theorem mul_kernel_is_wellformed : WellFormedKernel 2 mulKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [mulKernel, List.Vector.get_ofFn]
        norm_num
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (0 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [mulKernel, List.Vector.get_ofFn]
        norm_num

/-- 证明Div kernel function是良构的 -/
theorem div_kernel_is_wellformed : WellFormedKernel 2 divKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [divKernel, List.Vector.get_ofFn]
        -- 0/1 ≠ 1/1, 即 0 ≠ 1
        norm_num
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (2 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [divKernel, List.Vector.get_ofFn]
        -- 2/1 ≠ 2/2, 即 2 ≠ 1
        norm_num

/-- 证明Pow kernel function是良构的 -/
theorem pow_kernel_is_wellformed : WellFormedKernel 2 powKernel := by
  intro i
  fin_cases i
  · -- i = 0: 底数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (2 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (3 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [powKernel, List.Vector.get_ofFn]
        -- 2^2 ≠ 3^2, 即 4 ≠ 9
        norm_num
  · -- i = 1: 指数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (2 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (3 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [powKernel, List.Vector.get_ofFn]
        -- 2^2 ≠ 2^3, 即 4 ≠ 8
        norm_num

-- ===== 比较和逻辑算子Kernel良构性证明 =====

/-- 证明And kernel function是良构的 -/
theorem and_kernel_is_wellformed : WellFormedKernel 2 andKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [andKernel, List.Vector.get_ofFn]
        -- (0 ≠ 0) ∧ (1 ≠ 0) = false ∧ true = false ≠ (1 ≠ 0) ∧ (1 ≠ 0) = true ∧ true = true
        simp
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [andKernel, List.Vector.get_ofFn]
        -- (1 ≠ 0) ∧ (0 ≠ 0) = true ∧ false = false ≠ (1 ≠ 0) ∧ (1 ≠ 0) = true ∧ true = true
        simp

/-- 证明Or kernel function是良构的 -/
theorem or_kernel_is_wellformed : WellFormedKernel 2 orKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (0 : ℝ) else (0 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (0 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [orKernel, List.Vector.get_ofFn]
        -- (0 ≠ 0) ∨ (0 ≠ 0) = false ∨ false = false ≠ (1 ≠ 0) ∨ (0 ≠ 0) = true ∨ false = true
        simp
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (0 : ℝ) else (0 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (0 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [orKernel, List.Vector.get_ofFn]
        -- (0 ≠ 0) ∨ (0 ≠ 0) = false ∨ false = false ≠ (0 ≠ 0) ∨ (1 ≠ 0) = false ∨ true = true
        simp

/-- 证明Xor kernel function是良构的 -/
theorem xor_kernel_is_wellformed : WellFormedKernel 2 xorKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [xorKernel, List.Vector.get_ofFn]
        -- (0 ≠ 0) ≠ (1 ≠ 0) = false ≠ true = true ≠ (1 ≠ 0) ≠ (1 ≠ 0) = true ≠ true = false
        simp
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [xorKernel, List.Vector.get_ofFn]
        -- (1 ≠ 0) ≠ (0 ≠ 0) = true ≠ false = true ≠ (1 ≠ 0) ≠ (1 ≠ 0) = true ≠ true = false
        simp

/-- 证明Equal kernel function是良构的 -/
theorem equal_kernel_is_wellformed : WellFormedKernel 2 equalKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (2 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [equalKernel, List.Vector.get_ofFn]
        -- 1 = 2 is false ≠ 2 = 2 is true
        simp
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (2 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [equalKernel, List.Vector.get_ofFn]
        -- 2 = 1 is false ≠ 2 = 2 is true
        simp

/-- 证明Greater kernel function是良构的 -/
theorem greater_kernel_is_wellformed : WellFormedKernel 2 greaterKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (3 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [greaterKernel, List.Vector.get_ofFn]
        -- 1 > 2 is false ≠ 3 > 2 is true
        norm_num
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (3 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [greaterKernel, List.Vector.get_ofFn]
        -- 2 > 1 is true ≠ 2 > 3 is false
        norm_num

/-- 证明Less kernel function是良构的 -/
theorem less_kernel_is_wellformed : WellFormedKernel 2 lessKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (3 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [lessKernel, List.Vector.get_ofFn]
        -- 1 < 2 is true ≠ 3 < 2 is false
        norm_num
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (3 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [lessKernel, List.Vector.get_ofFn]
        -- 2 < 3 is true ≠ 2 < 1 is false
        norm_num

/-- 证明GreaterOrEqual kernel function是良构的 -/
theorem greaterOrEqual_kernel_is_wellformed : WellFormedKernel 2 greaterOrEqualKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (3 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [greaterOrEqualKernel, List.Vector.get_ofFn]
        -- 1 ≥ 2 is false ≠ 3 ≥ 2 is true
        norm_num
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (3 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [greaterOrEqualKernel, List.Vector.get_ofFn]
        -- 2 ≥ 3 is false ≠ 2 ≥ 1 is true
        norm_num

/-- 证明LessOrEqual kernel function是良构的 -/
theorem lessOrEqual_kernel_is_wellformed : WellFormedKernel 2 lessOrEqualKernel := by
  intro i
  fin_cases i
  · -- i = 0: 第一个参数不同
    use List.Vector.ofFn (fun j => if j.val = 0 then (3 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 0 then (1 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · contradiction
        · simp [List.Vector.get_ofFn]
      · simp only [lessOrEqualKernel, List.Vector.get_ofFn]
        -- 3 ≤ 2 is false ≠ 1 ≤ 2 is true
        norm_num
  · -- i = 1: 第二个参数不同
    use List.Vector.ofFn (fun j => if j.val = 1 then (1 : ℝ) else (2 : ℝ)),
        List.Vector.ofFn (fun j => if j.val = 1 then (3 : ℝ) else (2 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hj
        fin_cases j
        · simp [List.Vector.get_ofFn]
        · contradiction
      · simp only [lessOrEqualKernel, List.Vector.get_ofFn]
        -- 2 ≤ 1 is false ≠ 2 ≤ 3 is true
        norm_num


/-- 证明Max kernel function是良构的 -/
noncomputable def minKernel (n : ℕ) : KernelFunction n :=
  fun v =>
    if n = 0 then 0
    else (Finset.univ : Finset (Fin n)).image (fun i => v.get i) |>.min.getD 0

/-- Max kernel function: 计算n个输入中的最大值 -/
noncomputable def maxKernel (n : ℕ) : KernelFunction n :=
  fun v =>
    if n = 0 then 0
    else (Finset.univ : Finset (Fin n)).image (fun i => v.get i) |>.max.getD 0

/-- Mean kernel function: 计算n个输入的平均值 -/
noncomputable def meanKernel (n : ℕ) : KernelFunction n :=
  fun v =>
    if n = 0 then 0
    else (∑ i : Fin n, v.get i) / n

/-- Min SIMD函数 -/
noncomputable def minSIMD (dims : List ℕ) (input : MultiTensorInput) (n : ℕ)
    (h_input_count : input.p = n)
    (h_dims : ∀ i : Fin n, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createMultiaryElementwiseSIMD dims input n h_input_count h_dims (minKernel n)

/-- Max SIMD函数 -/
noncomputable def maxSIMD (dims : List ℕ) (input : MultiTensorInput) (n : ℕ)
    (h_input_count : input.p = n)
    (h_dims : ∀ i : Fin n, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createMultiaryElementwiseSIMD dims input n h_input_count h_dims (maxKernel n)

/-- Mean SIMD函数 -/
noncomputable def meanSIMD (dims : List ℕ) (input : MultiTensorInput) (n : ℕ)
    (h_input_count : input.p = n)
    (h_dims : ∀ i : Fin n, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    SIMDFunction input dims :=
  createMultiaryElementwiseSIMD dims input n h_input_count h_dims (meanKernel n)

-- ===== SIMD属性证明 =====

/-- 证明Min是SIMD函数 -/
theorem min_is_SIMD (dims : List ℕ) (input : MultiTensorInput) (n : ℕ)
    (h_input_count : input.p = n)
    (h_dims : ∀ i : Fin n, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (minSIMD dims input n h_input_count h_dims)) := by
  simp only [minSIMD]
  exact multiaryElementwise_is_SIMD dims input n h_input_count h_dims (minKernel n)

/-- 证明Max是SIMD函数 -/
theorem max_is_SIMD (dims : List ℕ) (input : MultiTensorInput) (n : ℕ)
    (h_input_count : input.p = n)
    (h_dims : ∀ i : Fin n, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (maxSIMD dims input n h_input_count h_dims)) := by
  simp only [maxSIMD]
  exact multiaryElementwise_is_SIMD dims input n h_input_count h_dims (maxKernel n)

/-- 证明Mean是SIMD函数 -/
theorem mean_is_SIMD (dims : List ℕ) (input : MultiTensorInput) (n : ℕ)
    (h_input_count : input.p = n)
    (h_dims : ∀ i : Fin n, input.dims.get ⟨i, by rw [h_input_count]; exact i.isLt⟩ = dims) :
    isSIMDFunction input dims
      (fun _ => applySIMD input dims (meanSIMD dims input n h_input_count h_dims)) := by
  simp only [meanSIMD]
  exact multiaryElementwise_is_SIMD dims input n h_input_count h_dims (meanKernel n)

-- ===== 良构性证明 =====

/-- 证明Min kernel function是良构的 -/
theorem min_kernel_is_wellformed (n : ℕ) : WellFormedKernel n (minKernel n) := by
  intro i
  by_cases h : n = 0
  · subst h; exact Fin.elim0 i
  · -- 构造两个向量：一个在位置i处为0，其他为1；另一个全为1
    use List.Vector.ofFn (fun j => if j = i then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun _ => (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hij
        simp [List.Vector.get_ofFn, hij]
      · classical
        simp only [minKernel, h, if_false, List.Vector.get_ofFn]
        set s1 := (Finset.univ : Finset (Fin n)).image (fun j => if j = i then (0 : ℝ) else 1) with hs1
        set s2 := (Finset.univ : Finset (Fin n)).image (fun _ => (1 : ℝ)) with hs2
        change s1.min.getD 0 ≠ s2.min.getD 0
        have h0_mem : (0 : ℝ) ∈ s1 := by
          simp [s1, hs1]
        have h1_mem : (1 : ℝ) ∈ s2 := by
          refine Finset.mem_image.mpr ?_
          refine ⟨⟨0, Nat.pos_of_ne_zero h⟩, Finset.mem_univ _, ?_⟩
          simp [hs2]
        have h_le_s1 : ((0 : ℝ) : WithTop ℝ) ≤ s1.min := by
          refine Finset.le_min ?_
          intro a ha
          rcases Finset.mem_image.mp ha with ⟨j, -, rfl⟩
          by_cases hji : j = i
          · subst hji; simp
          · simp [hji]
        have h_s1_le : s1.min ≤ ((0 : ℝ) : WithTop ℝ) := by
          simpa [hs1] using (Finset.min_le h0_mem)
        have hs1_min : s1.min = ((0 : ℝ) : WithTop ℝ) :=
          le_antisymm h_s1_le h_le_s1
        have h_le_s2 : ((1 : ℝ) : WithTop ℝ) ≤ s2.min := by
          refine Finset.le_min ?_
          intro a ha
          rcases Finset.mem_image.mp ha with ⟨j, -, rfl⟩
          simp [hs2]
        have h_s2_le : s2.min ≤ ((1 : ℝ) : WithTop ℝ) := by
          simpa [hs2] using (Finset.min_le h1_mem)
        have hs2_min : s2.min = ((1 : ℝ) : WithTop ℝ) :=
          le_antisymm h_s2_le h_le_s2
        have base : Option.getD (Option.some (0 : ℝ)) 0 ≠ Option.getD (Option.some (1 : ℝ)) 0 := by
          simp
        have : s1.min.getD 0 ≠ s2.min.getD 0 := by
          simpa [hs1_min, hs2_min, WithTop.some_eq_coe]
            using base
        simpa using this

/-- 证明Max kernel function是良构的 -/
theorem max_kernel_is_wellformed (n : ℕ) : WellFormedKernel n (maxKernel n) := by
  intro i
  by_cases h : n = 0
  · subst h; exact Fin.elim0 i
  · -- 构造两个向量：一个在位置i处为1，其他为0；另一个全为0
    use List.Vector.ofFn (fun j => if j = i then (1 : ℝ) else (0 : ℝ)),
        List.Vector.ofFn (fun _ => (0 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hij
        simp [List.Vector.get_ofFn, hij]
      · classical
        simp only [maxKernel, h, if_false, List.Vector.get_ofFn]
        set s1 := (Finset.univ : Finset (Fin n)).image (fun j => if j = i then (1 : ℝ) else 0) with hs1
        set s2 := (Finset.univ : Finset (Fin n)).image (fun _ => (0 : ℝ)) with hs2
        change s1.max.getD 0 ≠ s2.max.getD 0
        have h1_mem : (1 : ℝ) ∈ s1 := by
          refine Finset.mem_image.mpr ?_
          refine ⟨i, Finset.mem_univ i, ?_⟩
          simp [s1, hs1]
        have h0_mem : (0 : ℝ) ∈ s2 := by
          refine Finset.mem_image.mpr ?_
          refine ⟨⟨0, Nat.pos_of_ne_zero h⟩, Finset.mem_univ _, ?_⟩
          simp [s2, hs2]
        have h_le_s1 : s1.max ≤ ((1 : ℝ) : WithBot ℝ) := by
          refine Finset.max_le ?_
          intro a ha
          rcases Finset.mem_image.mp ha with ⟨j, -, rfl⟩
          by_cases hji : j = i
          · subst hji; simp
          · simp [hji]
        have h_s1_le : ((1 : ℝ) : WithBot ℝ) ≤ s1.max := by
          simpa [hs1] using (Finset.le_max h1_mem)
        have hs1_max : s1.max = ((1 : ℝ) : WithBot ℝ) :=
          le_antisymm h_le_s1 h_s1_le
        have h_le_s2 : s2.max ≤ ((0 : ℝ) : WithBot ℝ) := by
          refine Finset.max_le ?_
          intro a ha
          rcases Finset.mem_image.mp ha with ⟨j, -, rfl⟩
          simp
        have h_s2_le : ((0 : ℝ) : WithBot ℝ) ≤ s2.max := by
          simpa [hs2] using (Finset.le_max h0_mem)
        have hs2_max : s2.max = ((0 : ℝ) : WithBot ℝ) :=
          le_antisymm h_le_s2 h_s2_le
        have base : Option.getD (Option.some (1 : ℝ)) 0 ≠ Option.getD (Option.some (0 : ℝ)) 0 := by
          simp
        have : s1.max.getD 0 ≠ s2.max.getD 0 := by
          simpa [hs1_max, hs2_max, WithBot.some_eq_coe]
            using base
        simpa using this

/-- 证明Mean kernel function是良构的 -/

theorem mean_kernel_is_wellformed (n : ℕ) : WellFormedKernel n (meanKernel n) := by
  intro i
  by_cases h : n = 0
  · subst h; exact Fin.elim0 i
  · -- 构造两个向量，参照sum的证明思路
    use List.Vector.ofFn (fun j => if j = i then (0 : ℝ) else (1 : ℝ)),
        List.Vector.ofFn (fun _ => (1 : ℝ))
    constructor
    · simp [List.Vector.get_ofFn]
    · constructor
      · intro j hij
        simp [List.Vector.get_ofFn, hij]
      · simp only [meanKernel]
        simp [h]
        -- 第一个向量的平均值是(n-1)/n；第二个向量的平均值是1；它们不相等
        have n_pos : 0 < n := Nat.pos_of_ne_zero h
        have h1 : (∑ j : Fin n, if j = i then (0:ℝ) else 1) = (n:ℝ) - 1 := by
          -- 复用sum证明的逻辑
          have h_eq : (∑ j : Fin n, if j = i then (0:ℝ) else 1) =
                      ∑ j : Fin n, if j ≠ i then 1 else 0 := by
            congr 1; ext j
            by_cases hj : j = i <;> simp [hj]
          rw [h_eq, Finset.sum_boole]
          have h2 : Finset.filter (fun x => ¬x = i) Finset.univ = Finset.univ.erase i := by
            ext j; simp [Finset.mem_filter, Finset.mem_erase]
          rw [h2]
          simp [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
          rw [Nat.cast_sub (by linarith : 1 ≤ n), Nat.cast_one]

        have h2 : (∑ j : Fin n, (1:ℝ)) = (n:ℝ) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

        -- 证明 (n-1)/n ≠ 1
        have final : ((n:ℝ) - 1) / (n:ℝ) ≠ 1 := by
          field_simp
        -- 应用h1和h2来转换目标
        rw [h1]
        simp [h2]
        exact final

end SIMD
