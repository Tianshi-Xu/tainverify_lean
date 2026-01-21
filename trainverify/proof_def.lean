import Mathlib.Data.Vector.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Defs

namespace TrainVerify

/-! # 形式化定义与推导步骤

本文件包含了 TrainVerify 论文中 Shape Reduction Correctness Proof 的 Lean4 形式化。

## 目录
1. 基础定义 (张量、函数)
2. SIMD 函数相关定义
3. 其他函数与属性定义
4. SMT 求解器的前提
5. 正确性证明

-/

/-! ### 1. 基础定义 -/

/-- **定义 1.1 (张量 Tensor)**
一个 n 阶张量 T 是张量空间 ℝ^(d1 × d2 × ... × dn) 中的一个元素。
我们使用函数表示张量：从多维索引到实数的映射。
-/
def def1_1_Tensor (dims : List ℕ) : Type :=
  (List.Vector ℕ dims.length) → ℝ

/-- 多维索引类型 -/
def Index (n : ℕ) : Type := List.Vector ℕ n

/-- 检查索引是否有效 -/
def validIndex (dims : List ℕ) (idx : Index dims.length) : Prop :=
  ∀ i : Fin dims.length, idx.get i < dims.get i

/-- **定义 1.2 (函数 Function)**
一个函数 f 将一个输入张量 x 映射到一个输出张量 y。
-/
def def1_2_TensorFunction (input_dims output_dims : List ℕ) : Type :=
  def1_1_Tensor input_dims → def1_1_Tensor output_dims

/-! ### 2. SIMD 函数相关定义 -/

/-- **定义 2.1 (核函数 Kernel Function)**
核函数 θ 是一个接受 k 个标量输入并产生一个标量输出的函数。
符号表示: θ: ℝ^k → ℝ
-/
def def2_1_KernelFunction (k : ℕ) : Type :=
  (List.Vector ℝ k) → ℝ

/-- **定义 2.2 (依赖映射 Dependency Mapping)**
对于一个函数 f(x) → y，其依赖映射 τ 将输出张量 y 的每个索引 i
映射到输入张量 x 的一个索引列表。
符号表示: τ: ℕ^n → ℕ^(k × m)
-/
def def2_2_DependencyMapping (n m k : ℕ) : Type :=
  Index n → List.Vector (Index m) k

/-- **定义 2.3 (SIMD 函数 SIMD Function)**
一个函数 f(x) → y 如果满足以下条件，则被称为 SIMD 函数
-/
structure def2_3_SIMDFunction (input_dims output_dims : List ℕ) where
  k : ℕ  -- 核函数的输入数量
  kernel : def2_1_KernelFunction k  -- 核函数
  dependency : def2_2_DependencyMapping output_dims.length input_dims.length k  -- 依赖映射

/-- 应用 SIMD 函数到特定输出索引 -/
def applySIMDAt (input_dims output_dims : List ℕ)
    (f : def2_3_SIMDFunction input_dims output_dims)
    (x : def1_1_Tensor input_dims)
    (i : Index output_dims.length) : ℝ :=
  let input_indices := f.dependency i
  let input_values := List.Vector.map (fun idx => x idx) input_indices
  f.kernel input_values

/-- 完整的 SIMD 函数应用 -/
def applySIMD (input_dims output_dims : List ℕ)
    (f : def2_3_SIMDFunction input_dims output_dims)
    (x : def1_1_Tensor input_dims) : def1_1_Tensor output_dims :=
  fun i => applySIMDAt input_dims output_dims f x i

/-- **定义 2.4 (线性依赖映射)**
在 LLM 算子中，依赖映射 τ 通常是仿射变换
-/
structure def2_4_AffineDependencyMapping (n m k : ℕ) where
  -- 基础依赖映射
  toMapping : def2_2_DependencyMapping n m k
  -- 变换矩阵 M 和偏移向量 b_j，全部在 ℕ 上表示
  M : Matrix (Fin m) (Fin n) ℕ
  offsets : List.Vector (List.Vector ℕ m) k
  affine :
    ∀ (i : Index n) (j : Fin k) (t : Fin m),
      ((toMapping i).get j).get t =
        Matrix.mulVec M (fun s => (i.get s)) t + (offsets.get j).get t

/-- Cast an affine dependency mapping along an equality of arities. -/
def def2_4_AffineDependencyMapping.castLength {n m k₁ k₂ : ℕ}
    (h : k₁ = k₂) (aff : def2_4_AffineDependencyMapping n m k₁) :
    def2_4_AffineDependencyMapping n m k₂ := by
  cases h
  simpa using aff


/-! ### 3. 其他函数与属性定义 -/

/-- **定义 3.1 (归约函数 Reductional Function)**
对于输入张量 x ∈ ℝ^m，归约函数 f_⊙ 应用一个二元操作 ⊙ 于 x 的所有元素
-/
structure def3_1_ReductionalFunction (input_size : ℕ) where
  op : ℝ → ℝ → ℝ  -- 二元操作 ⊙
  commutative : ∀ a b, op a b = op b a  -- 交换律
  associative : ∀ a b c, op (op a b) c = op a (op b c)  -- 结合律

/-- 应用归约函数 -/
def applyReduction (input_size : ℕ) (f : def3_1_ReductionalFunction input_size)
    (x : List.Vector ℝ input_size) : ℝ :=
  match input_size with
  | 0 => 0  -- 空输入的默认值
  | n + 1 =>
    let rec fold (i : ℕ) (acc : ℝ) : ℝ :=
      if h : i < n + 1 then
        fold (i + 1) (f.op acc (x.get ⟨i, h⟩))
      else
        acc
    if h : 0 < n + 1 then
      fold 1 (x.get ⟨0, h⟩)
    else
      0

/-- **定义 3.2 (映射置换等价 Mapping Permutation Equivalence)**
对于两个依赖映射 τ₁ 和 τ₂，如果存在一个置换函数 P，使得对于任意索引 i，
都有 P(τ₁(i)) = τ₂(i)，则称 τ₁ 和 τ₂ 是映射置换等价的。
-/
def def3_2_MappingPermutationEquivalent {n m k : ℕ}
    (τ₁ τ₂ : def2_2_DependencyMapping n m k) : Prop :=
  ∃ (P : Equiv.Perm (Fin k)),
    ∀ (i : Index n),
      List.Vector.ofFn (fun j => (τ₁ i).get (P j)) = τ₂ i

notation:50 τ₁ " ≃ₚ " τ₂ => def3_2_MappingPermutationEquivalent τ₁ τ₂

/-- **定义 3.3 (核函数置换集等价 Kernel Permutation-set Equivalence)**
对于两个核函数 θ₁ 和 θ₂，如果存在一个非空的置换函数集合 Q，使得对于集合中的
任意置换 P ∈ Q 和任意输入 x，都有 θ₁(x) = θ₂(P(x))，则称 θ₁ 和 θ₂ 是核函数置换集等价的。
-/
def def3_3_KernelPermutationSetEquivalent {k : ℕ}
    (θ₁ θ₂ : def2_1_KernelFunction k) : Prop :=
  ∃ (Q : Set (Equiv.Perm (Fin k))), Q.Nonempty ∧
    ∀ (P : Equiv.Perm (Fin k)), P ∈ Q →
      ∀ (x : List.Vector ℝ k),
        θ₁ x = θ₂ (List.Vector.ofFn (fun i => x.get (P i)))

notation:50 θ₁ " ≃Q " θ₂ => def3_3_KernelPermutationSetEquivalent θ₁ θ₂

/-- **定义 3.4 (良构核函数 Well-formed Kernel Function)**
一个核函数 θ 被称为良构的，如果任意单个输入元素的改变都会导致输出的改变。
-/
def def3_4_WellFormedKernel {k : ℕ} (θ : def2_1_KernelFunction k) : Prop :=
  ∀ (i : Fin k) (x x' : List.Vector ℝ k),
    (∀ j : Fin k, j ≠ i → x.get j = x'.get j) →
    x.get i ≠ x'.get i →
    θ x ≠ θ x'

/-- **定义 3.5 (无重复输入索引)**
在实践中，对于任意输出索引 i，依赖映射 τ(i) 产生的输入索引列表中不包含重复的索引。
-/
def def3_5_NoRepeatedIndices {n m k : ℕ} (τ : def2_2_DependencyMapping n m k) : Prop :=
  ∀ (i : Index n) (a b : Fin k), a ≠ b →
    (τ i).get a ≠ (τ i).get b

/-! ### 4. SMT 求解器的前提 -/

/-- 标准基向量 e_i，其中 e_0 是零向量 -/
def basisVector (n : ℕ) (i : Fin (n + 1)) : Index n :=
  List.Vector.ofFn fun j => if i.val = 0 then 0 else if j.val + 1 = i.val then 1 else 0

/-- **定义 4.1 (SMT 前提)**
TrainVerify 使用 SMT 求解器在形状缩减的模型上验证等价性。
如果求解器返回 sat，则对于所有输入 x 和特定的索引子集 I，以下等式成立：
f(x)[i] = g(x)[i], ∀x, ∀i ∈ I

其中 I = { Σ_{j=0}^{n} a_j * e_j | a_j ∈ {0, 1} }
-/
def def4_1_VertexIndexSet (n : ℕ) : Set (Index n) :=
  { i | ∀ j : Fin n, i.get j = 0 ∨ i.get j = 1 }

/-- SMT 前提：在顶点索引集上的等价性 -/
def def4_1_SMTPremise (input_dims output_dims : List ℕ)
    (f g : def1_2_TensorFunction input_dims output_dims) : Prop :=
  ∀ (x : def1_1_Tensor input_dims) (i : Index output_dims.length),
    i ∈ def4_1_VertexIndexSet output_dims.length →
    f x i = g x i

/-! ### 5. 正确性证明的引理和定理 -/

open Classical

section ShapeReduction

variable {input_dims output_dims : List ℕ}

/-- Cast a kernel function across equal arities. This is a thin wrapper around
the underlying heterogeneous equality and is convenient for aligning the arity
of two SIMD kernels when we already know their `k` fields agree. -/
def def2_1_KernelFunction.castLength {k₁ k₂ : ℕ}
    (h : k₁ = k₂) (θ : def2_1_KernelFunction k₁) : def2_1_KernelFunction k₂ := by
  cases h
  simpa using θ

lemma def2_1_KernelFunction.castLength_eval {k₁ k₂ : ℕ}
    (h : k₁ = k₂) (θ : def2_1_KernelFunction k₁) (x : List.Vector ℝ k₂) :
    def2_1_KernelFunction.castLength h θ x =
      θ (List.Vector.ofFn fun i : Fin k₁ => x.get (Fin.cast h i)) := by
  cases h
  simp [def2_1_KernelFunction.castLength]

/-- Cast a dependency mapping across equal kernel arities. This mirrors
`KernelFunction.castLength` and allows us to compare vectors that come from
different SIMD functions but have the same logical length. -/
def def2_2_DependencyMapping.castLength {n m k₁ k₂ : ℕ}
    (h : k₁ = k₂) (τ : def2_2_DependencyMapping n m k₁) :
    def2_2_DependencyMapping n m k₂ := by
  cases h
  simpa using τ

lemma dependency_cast_get {n m k₁ k₂ : ℕ}
    (h : k₁ = k₂) (τ : def2_2_DependencyMapping n m k₁)
    (i : Index n) (a : Fin k₂) :
    (def2_2_DependencyMapping.castLength h τ i).get a =
      (τ i).get (Fin.cast h.symm a) := by
  cases h
  simp [def2_2_DependencyMapping.castLength]

lemma Fin.cast_cast_symm {k₁ k₂ : ℕ} (h : k₁ = k₂) (a : Fin k₂) :
    Fin.cast h (Fin.cast h.symm a) = a := by
  cases h
  simp

lemma Fin.cast_symm_cast {k₁ k₂ : ℕ} (h : k₁ = k₂) (a : Fin k₁) :
    Fin.cast h.symm (Fin.cast h a) = a := by
  cases h
  simp

@[simp] lemma affine_castLength_toMapping {n m k₁ k₂ : ℕ}
    (h : k₁ = k₂) (aff : def2_4_AffineDependencyMapping n m k₁) :
    (def2_4_AffineDependencyMapping.castLength h aff).toMapping =
      def2_2_DependencyMapping.castLength h aff.toMapping := by
  cases h
  simp [def2_4_AffineDependencyMapping.castLength,
    def2_2_DependencyMapping.castLength]

end ShapeReduction


end TrainVerify
