### 支持任意输入张量的形式化SIMD算子定义

此定义将原有的单个输入张量框架扩展，以支持一个函数接收任意数量的输入张量，并产生一个输出张量。

#### 第1步：符号定义

* **输入张量 (Input Tensors)**:
    * 一个由 $p$ 个张量组成的元组 (tuple)，记为 $\mathcal{X} = (X_1, X_2, \dots, X_p)$。
    * 每个输入张量 $X_j$ 都有其各自的维度 $dims_j = [d_{j,1}, \dots, d_{j, m_j}]$，其中 $m_j$ 是张量 $X_j$ 的阶数 (rank)。

* **输出张量 (Output Tensor)**:
    * 一个单一的输出张量 $Y$，其维度为 $dims_{out} = [d'_{1}, \dots, d'_{n}]$，其中 $n$ 是 $Y$ 的阶数。

* **函数 (Function)**:
    * 一个将 $p$ 个输入张量映射到一个输出张量的函数 $f$，记为 $f(X_1, X_2, \dots, X_p) \rightarrow Y$。

* **输入指针 (Input Pointer)**:
    * 一个二元组 $(\mathbb{N}, \text{Index})$，用于唯一地定位任意一个输入张量中的一个具体元素。
    * 第一个元素 `tensor_idx` ($0 \le \text{tensor\_idx} < p$) 指明是第几个输入张量。
    * 第二个元素 `multi_dim_idx` 是该张量内的多维索引。

* **其他符号**:
    * $k$: 核函数 $\theta$ 所需的标量输入总数量。
    * $\theta$: 核函数。
    * $\tau$: 依赖映射。
    * $\mathbb{R}$: 实数域。
    * $\mathbb{N}$: 自然数集。

---

#### 第2步：定义核函数 (Kernel Function) $\theta$

核函数的定义保持不变，它依然是整个SIMD运算的核心计算逻辑。

* **定义**: 核函数是一个接收 $k$ 个标量输入并产生一个标量输出的函数。
* **形式化**:
    $$ \theta: \mathbb{R}^k \rightarrow \mathbb{R} $$

---

#### 第3步：定义通用依赖映射 (Generalized Dependency Mapping) $\tau$

依赖映射的定义被扩展，使其能够指向多个输入张量。

* **定义**: 通用依赖映射将输出张量 $Y$ 的每一个索引 $\mathbf{i}_{out}$，映射到一个包含 $k$ 个**输入指针**的列表。
* **形式化**:
    $$ \tau: \text{Index}(dims_{out}) \rightarrow [(\text{tensor\_idx}_1, \mathbf{i}_1), (\text{tensor\_idx}_2, \mathbf{i}_2), \dots, (\text{tensor\_idx}_k, \mathbf{i}_k)] $$
    * 对于列表中的第 $j$ 个元素 $(\text{tensor\_idx}_j, \mathbf{i}_j)$：
        * `tensor_idx`$_j$ 指定了要从输入元组 $\mathcal{X}$ 中选择的张量 $X_{\text{tensor\_idx}_j}$。
        * $\mathbf{i}_j$ 是用于在张量 $X_{\text{tensor\_idx}_j}$ 内定位元素的多维索引。

---

#### 第4步：组合定义通用SIMD函数

一个函数 $f(X_1, \dots, X_p) \rightarrow Y$ 是一个SIMD函数，当且仅当对于输出张量 $Y$ 中的每一个元素 $Y[\mathbf{i}_{out}]$，其计算过程满足以下步骤：

1.  对于任意一个输出索引 $\mathbf{i}_{out}$，通过通用依赖映射函数 $\tau$ 获得一个包含 $k$ 个输入指针的列表：
    $$ \text{pointers} = \tau(\mathbf{i}_{out}) $$

2.  遍历这个指针列表，从对应的输入张量中获取 $k$ 个标量值。对于列表中的第 $j$ 个指针 $(\text{tensor\_idx}_j, \mathbf{i}_j)$，其对应的标量值为：
    $$ v_j = X_{\text{tensor\_idx}_j}[\mathbf{i}_j] $$

3.  将这 $k$ 个标量值 $v_1, v_2, \dots, v_k$ 作为输入，应用核函数 $\theta$ 来计算输出元素 $Y[\mathbf{i}_{out}]$ 的值：
    $$ Y[\mathbf{i}_{out}] = \theta(v_1, v_2, \dots, v_k) $$

综上，一个通用SIMD函数可以被统一表示为：
$$ Y[\mathbf{i}_{out}] = \theta \left( \left( X_{\text{ptr.tensor\_idx}}[\text{ptr.multi\_dim\_idx}] \right)_{\text{ptr} \in \tau(\mathbf{i}_{out})} \right) $$



#### 良构核函数定义

一个更严谨和清晰的形式化描述如下：

* **通俗描述**:
    一个核函数 $\theta$ 是**良构**的，如果对于它的任意一个输入位置 `i`，我们总能找到两个输入向量 `v` 和 `v'`，这两个向量仅在位置 `i` 的值不同，而在所有其他位置 `j` 的值都完全相同，并且函数 $\theta$ 对这两个不同向量的计算结果也必然不同。

* **形式化**:
    令核函数为 $\theta: \mathbb{R}^k \rightarrow \mathbb{R}$，其输入为向量 $\mathbf{v} \in \mathbb{R}^k$。
    $\theta$ 是良构的，当且仅当对于**任意**输入位置 $i \in \{1, 2, \dots, k\}$，都**存在**两个向量 $\mathbf{v}, \mathbf{v}' \in \mathbb{R}^k$，满足以下两个条件：
    1.  两个向量仅在位置 $i$ 不同：
        $$\mathbf{v}[i] \neq \mathbf{v}'[i] \quad \text{且} \quad \forall j \neq i, \mathbf{v}[j] = \mathbf{v}'[j]$$
    2.  函数的输出也随之不同：
        $$\theta(\mathbf{v}) \neq \theta(\mathbf{v}')$$
