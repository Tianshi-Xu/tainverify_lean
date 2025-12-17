### 1. 矩阵乘法 (Matrix Multiplication)

#### **1.1. 形式化数学描述**

* **符号定义**:
    * **输入**: 两个二维张量（矩阵） $A$ 和 $B$。
    * **维度**:
        * $A$ 的维度为 $[M, P]$。
        * $B$ 的维度为 $[P, N]$。
    * **输出**: 一个二维张量 $C$，维度为 $[M, N]$。
    * **索引**:
        * $\mathbf{i} = \langle i, j \rangle$ 是输出张量 $C$ 的一个二维索引，其中 $0 \le i < M, 0 \le j < N$。
        * $k$ 是求和所用的内部索引，其中 $0 \le k < P$。

* **运算**:
    输出张量 $C$ 中在位置 $\langle i, j \rangle$ 的元素值，等于输入张量 $A$ 的第 $i$ 行与张量 $B$ 的第 $j$ 列的点积。

    $$ \forall \langle i, j \rangle, \quad C[i, j] = \sum_{k=0}^{P-1} A[i, k] \cdot B[k, j] $$

#### **1.2. SIMD函数表示法 (多张量输入)**

* **输入**: 一个包含两个张量的元组 $\mathcal{X} = (A, B)$。其中 $X_1 = A, X_2 = B$。
* **输入维度**:
    * $dims_1 = [M, P]$
    * $dims_2 = [P, N]$
* **输出维度**: $dims_{out} = [M, N]$

* **k值 (核函数输入数量)**:
    计算一个输出元素需要 $A$ 的一行（$P$个元素）和 $B$ 的一列（$P$个元素）。
    $$ k = 2P $$

* **核函数 (Kernel Function) $\theta$**:
    核函数接收一个长度为 $2P$ 的向量 $\mathbf{v}$，其中前 $P$ 个元素来自 $A$ 的行，后 $P$ 个元素来自 $B$ 的列，并计算它们的点积。
    $$ \theta: \mathbb{R}^{2P} \rightarrow \mathbb{R} $$
    $$ \theta(\mathbf{v}) = \sum_{k=0}^{P-1} \mathbf{v}[k] \cdot \mathbf{v}[k+P] $$

* **依赖映射 (Dependency Mapping) $\tau$**:
    对于输出索引 $\mathbf{i}_{out} = \langle i, j \rangle$，依赖映射需要生成 $2P$ 个输入指针，分别指向 $A$ 的第 $i$ 行和 $B$ 的第 $j$ 列。
    $$ \tau(\langle i, j \rangle) = \left[ \begin{array}{l} (1, \langle i, 0 \rangle), (1, \langle i, 1 \rangle), \dots, (1, \langle i, P-1 \rangle), \\ (2, \langle 0, j \rangle), (2, \langle 1, j \rangle), \dots, (2, \langle P-1, j \rangle) \end{array} \right] $$
    * *(注: 这里 `(1, ...)` 表示指向第一个张量A, `(2, ...)` 表示指向第二个张量B)*

#### **1.3. 核函数良构证明 (Well-formedness Proof)**

**目标**: 证明核函数 $\theta(\mathbf{v}) = \sum_{k=0}^{P-1} \mathbf{v}[k] \cdot \mathbf{v}[k+P]$ 是良构的（假设 $P \ge 1$）。

**良构定义**: 对于任意输入位置 $l \in \{0, \dots, 2P-1\}$，都存在向量 $\mathbf{v}, \mathbf{v}'$，使得 $\mathbf{v}[l] \neq \mathbf{v}'[l]$ 且对于所有 $m \neq l$, $\mathbf{v}[m] = \mathbf{v}'[m]$，并且 $\theta(\mathbf{v}) \neq \theta(\mathbf{v}')$。

**证明**:
我们将对任意输入位置 $l$ 分两种情况讨论。

* **情况 1: $l$ 在前半部分 ($0 \le l < P$)**
    1.  **选取**: 任取一个输入位置 $l$ 使得 $0 \le l < P$。
    2.  **构造向量**: 我们需要构造两个仅在位置 $l$ 不同的向量 $\mathbf{v}, \mathbf{v}'$。
        * 令向量 $\mathbf{v}$ 的所有元素均为 1。即 $\forall m \in \{0, \dots, 2P-1\}, \mathbf{v}[m] = 1$。
        * 令向量 $\mathbf{v}'$ 与 $\mathbf{v}$ 在所有位置都相同，除了位置 $l$。令 $\mathbf{v}'[l] = 2$。
    3.  **验证前提**:
        * $\mathbf{v}[l] = 1, \mathbf{v}'[l] = 2 \implies \mathbf{v}[l] \neq \mathbf{v}'[l]$。
        * 对于任意 $m \neq l$, $\mathbf{v}'[m] = 1 = \mathbf{v}[m]$。前提条件满足。
    4.  **计算 $\theta(\mathbf{v})$**:
        $$ \theta(\mathbf{v}) = \sum_{k=0}^{P-1} \mathbf{v}[k] \cdot \mathbf{v}[k+P] = \sum_{k=0}^{P-1} 1 \cdot 1 = P $$
    5.  **计算 $\theta(\mathbf{v}')$**:
        求和式中只有第 $l$ 项受到影响。
        $$ \theta(\mathbf{v}') = (\sum_{k=0, k \neq l}^{P-1} \mathbf{v}'[k] \cdot \mathbf{v}'[k+P]) + (\mathbf{v}'[l] \cdot \mathbf{v}'[l+P]) $$
        $$ = (\sum_{k=0, k \neq l}^{P-1} 1 \cdot 1) + (2 \cdot 1) = (P-1) + 2 = P+1 $$
    6.  **比较结果**: $\theta(\mathbf{v}) = P$ 且 $\theta(\mathbf{v}') = P+1$，因此 $\theta(\mathbf{v}) \neq \theta(\mathbf{v}')$。
    7.  **结论**: 对于任意 $0 \le l < P$，该定义成立。

* **情况 2: $l$ 在后半部分 ($P \le l < 2P$)**
    1.  **选取**: 任取一个输入位置 $l$ 使得 $P \le l < 2P$。令 $l' = l - P$，则 $0 \le l' < P$。
    2.  **构造向量**:
        * 令向量 $\mathbf{v}$ 的所有元素均为 1。
        * 令向量 $\mathbf{v}'$ 与 $\mathbf{v}$ 在所有位置都相同，除了位置 $l$。令 $\mathbf{v}'[l] = 2$。
    3.  **计算 $\theta(\mathbf{v})$**: $\theta(\mathbf{v}) = P$。
    4.  **计算 $\theta(\mathbf{v}')$**:
        求和式中只有第 $l'$ 项受到影响。
        $$ \theta(\mathbf{v}') = (\sum_{k=0, k \neq l'}^{P-1} \mathbf{v}'[k] \cdot \mathbf{v}'[k+P]) + (\mathbf{v}'[l'] \cdot \mathbf{v}'[l'+P]) $$
        $$ = (\sum_{k=0, k \neq l'}^{P-1} 1 \cdot 1) + (1 \cdot \mathbf{v}'[l]) = (P-1) + (1 \cdot 2) = P+1 $$
    5.  **比较结果**: $\theta(\mathbf{v}) = P$ 且 $\theta(\mathbf{v}') = P+1$，因此 $\theta(\mathbf{v}) \neq \theta(\mathbf{v}')$。
    6.  **结论**: 对于任意 $P \le l < 2P$，该定义成立。

**最终结论**: 由于两种情况覆盖了所有可能的输入位置 $l$，我们证明了矩阵乘法的核函数是**良构**的。

---

### 2. ReLU 激活函数 (ReLU Activation)

#### **2.1. 形式化数学描述**

* **符号定义**:
    * **输入**: 一个任意维度的张量 $A$。
    * **维度**: $A$ 的维度为 $dims = [d_1, d_2, \dots, d_n]$。
    * **输出**: 一个与输入张量维度相同的张量 $B$。
    * **索引**: $\mathbf{i}$ 是一个适用于 $A$ 和 $B$ 的任意有效多维索引。

* **运算**:
    输出张量 $B$ 的每个元素是输入张量 $A$ 对应元素与0的最大值。

    $$ \forall \mathbf{i}, \quad B[\mathbf{i}] = \max(0, A[\mathbf{i}]) $$

#### **2.2. SIMD函数表示法 (单张量输入)**

* **输入**: 一个包含单个张量的元组 $\mathcal{X} = (A)$。
* **输入维度**: $dims_1 = dims$。
* **输出维度**: $dims_{out} = dims$。

* **k值 (核函数输入数量)**:
    $$ k = 1 $$

* **核函数 (Kernel Function) $\theta$**:
    核函数接收一个标量并返回其与0的最大值。
    $$ \theta: \mathbb{R}^1 \rightarrow \mathbb{R} $$
    $$ \theta(v_1) = \max(0, v_1) $$

* **依赖映射 (Dependency Mapping) $\tau$**:
    输出索引 $\mathbf{i}$ 仅依赖于第一个（也是唯一一个）输入张量中相同位置的索引。
    $$ \tau(\mathbf{i}) = [(1, \mathbf{i})] $$

#### **2.3. 核函数良构证明 (Well-formedness Proof)**

**目标**: 证明核函数 $\theta(v_1) = \max(0, v_1)$ 是良构的。

**良构定义**: 对于任意输入位置 $l \in \{0, \dots, k-1\}$... 由于 $k=1$，我们只需证明对于 $l=0$ 的情况成立。
即，存在两个标量 $v_1, v'_1$ 使得 $v_1 \neq v'_1$ 且 $\theta(v_1) \neq \theta(v'_1)$。

**证明**:
1.  **选取**: 唯一的输入位置是 $l=0$。
2.  **构造标量**: 我们需要构造两个不同的标量 $v_1, v'_1$。
    * 令 $v_1 = 1$。
    * 令 $v'_1 = 2$。
3.  **验证前提**:
    * $v_1 \neq v'_1$ 因为 $1 \neq 2$。前提满足。
4.  **计算 $\theta(v_1)$**:
    $$ \theta(v_1) = \max(0, 1) = 1 $$
5.  **计算 $\theta(v'_1)$**:
    $$ \theta(v'_1) = \max(0, 2) = 2 $$
6.  **比较结果**: $\theta(v_1) = 1$ 且 $\theta(v'_1) = 2$，因此 $\theta(v_1) \neq \theta(v'_1)$。

**最终结论**: 我们成功构造了一对满足条件的输入，因此证明了ReLU的核函数是**良构**的。
