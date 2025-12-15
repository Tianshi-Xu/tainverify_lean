-- 为了方便，我们为向量（从 Fin n 到 Float 的函数）创建一个类型别名
abbrev Vector (n : Nat) := Fin n → Float

/-- 计算矩阵每一行的最大值 -/
def rowMax {m n : Nat} (A : Matrix Float m n) : Vector m :=
  fun i => Id.run do
    let mut max_val := Float.negInfinity
    for k in Fin.range n do
      max_val := max max_val (A i k)
    return max_val

/-- 计算矩阵每一行的元素和 -/
def rowSum {m n : Nat} (A : Matrix Float m n) : Vector m :=
  fun i => Id.run do
    let mut sum := 0.0
    for k in Fin.range n do
      sum := sum + (A i k)
    return sum

def flashAttention
    -- 类型参数：序列长度 N，头维度 d
    {N d : Nat}
    -- 输入：Q, K, V 矩阵，以及模拟 SRAM 大小的参数 M
    (Q K V : Matrix Float N d) (M : Nat)
    : Matrix Float N d :=

  -- 步骤 1: 设置块大小
  -- 为了简化，我们假设 N, d, M 的值使得除法是整除的
  let B_c := M / (4 * d)
  let B_r := min (M / (4 * d)) d
  let T_r := N / B_r
  let T_c := N / B_c

  -- 步骤 2: 初始化 O, ℓ, m (在 HBM 中)
  let mut O : Matrix Float N d := fun _ _ => 0.0
  let mut ℓ : Vector N := fun _ => 0.0
  let mut m : Vector N := fun _ => Float.negInfinity

  -- 步骤 5: 外层循环，遍历 K 和 V 的块
  for j_idx in List.range T_c do
    let j := Fin.ofNat j_idx

    -- 步骤 6: 从 HBM 加载 K_j, V_j 到 SRAM
    -- 我们通过创建子矩阵来模拟这个过程
    let Kj : Matrix Float B_c d := fun r c => K (Fin.ofNat (j * B_c + r)) c
    let Vj : Matrix Float B_c d := fun r c => V (Fin.ofNat (j * B_c + r)) c

    -- 步骤 7: 内层循环，遍历 Q 的块
    for i_idx in List.range T_r do
      let i := Fin.ofNat i_idx

      -- 步骤 8: 从 HBM 加载 Q_i, O_i, ℓ_i, m_i 到 SRAM
      let Qi : Matrix Float B_r d  := fun r c => Q (Fin.ofNat (i * B_r + r)) c
      let Oi : Matrix Float B_r d  := fun r c => O (Fin.ofNat (i * B_r + r)) c
      let ℓi : Vector B_r          := fun r   => ℓ (Fin.ofNat (i * B_r + r))
      let mi : Vector B_r          := fun r   => m (Fin.ofNat (i * B_r + r))

      -- == 片上计算 (On-chip computation) ==

      -- 步骤 9: 计算 S_ij = Q_i * K_j^T
      let S_ij := Qi * Kj.transpose

      -- 步骤 10: 计算逐行的统计数据
      let m_tilde_ij := rowMax S_ij
      let P_tilde_ij := Matrix.of fun r c => (S_ij r c - m_tilde_ij r).exp
      let ℓ_tilde_ij := rowSum P_tilde_ij

      -- 步骤 11: 计算新的 m 和 ℓ
      let m_i_new := fun r => max (mi r) (m_tilde_ij r)
      let ℓ_i_new := fun r =>
        (mi r - m_i_new r).exp * (ℓi r) +
        (m_tilde_ij r - m_i_new r).exp * (ℓ_tilde_ij r)

      -- 步骤 12: 更新输出 O_i
      -- 通过创建新的 O_i 块来模拟更新
      let P_V := P_tilde_ij * Vj
      let O_i_new := Matrix.of fun r c =>
        (1.0 / ℓ_i_new r) * (
          (ℓi r) * (mi r - m_i_new r).exp * (Oi r c) +
          (m_tilde_ij r - m_i_new r).exp * (P_V r c)
        )

      -- == 写回 HBM ==
      -- 步骤 12 & 13: 将更新后的块写回全局 O, ℓ, m
      -- 这在函数式语言中通常意味着创建一个新的、更新后的数据结构
      O := O.updateRow i O_i_new -- 这是一个简化的写法，实际需要一个 `updateBlock` 函数
      m := fun idx => if i * B_r ≤ idx.val ∧ idx.val < (i + 1) * B_r then m_i_new (Fin.ofNat (idx.val - i * B_r)) else m idx
      ℓ := fun idx => if i * B_r ≤ idx.val ∧ idx.val < (i + 1) * B_r then ℓ_i_new (Fin.ofNat (idx.val - i * B_r)) else ℓ idx

  -- 步骤 15: 返回最终的 O
  return O
