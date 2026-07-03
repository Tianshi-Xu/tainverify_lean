# Denote Op Semantics Audit — 2026-07-03 (v3, subagent-augmented)

## TL;DR

**GPT-2 (312 桥) audit 结果**：**层次 3 clean（0 custom axiom）**，但 subagent 深入 audit 发现 **1 个真实 semantic mismatch bug（`bw_softmax`）**+ 多个 CONDITIONAL 前提。

**Pattern_2/4/5**：L1 ✅ L3 ✅ L2 主要 ops (embedding, topk_routing, inner_chunk_ce, stack) verified。

**Pattern_1**：仍然 vacuous。

---

## GPT-2 Layer 2 subagent audit — key findings

### VERIFIED (semantics match Python for GPT-2 usage)

- `fw_sum`, `bw_sum`: 数值正确（shape [1] vs `()` 差异不影响）
- `fw_gelu` / `bw_gelu`: **exact GELU (erf-based)**. GPT-2 nanogpt fixture uses `F.gelu` (default = exact) ✅ 匹配
- `fw_linear`, `bw_linear`: `y = x @ w.T` 语义正确（2D/3D only）
- `fw_matmul` / `batchedMatmul`, `bw_matmul`: batch 前缀严格相同时正确
- `fw_softmax`: standard softmax ✅
- `fw_multiref`, `fw_contiguous`, `bw_contiguous`, `fw_transpose`, `bw_transpose`: 精确 verified
- `fw_view`: numel 相等时正确（GPT-2 always numel-preserving）

### CONDITIONAL (前提在 GPT-2 用例下满足)

- `elemwiseAdd/elemwiseMul`: `outShape2` 只按 length 选 first arg（不是 PyTorch full broadcasting）。**GPT-2 里 45 处 FW_add 全 same-shape，满足条件** ✅
- `fw_div` / `bw_div`: 除数被限制为 `Nat`（无法表达 `1/√d_k`）。**GPT-2 里 FW_div `params := [2]` (除以 2)，满足** ✅
- `fw_embedding`, `bw_embedding`: weight 必须 2D，满足；不建模 padding_idx/sparse
- `fw_layernorm`, `bw_layernorm`: 仅单尾维归一化 + eps=1e-5 hardcoded。GPT-2 fixture 满足
- `bw_multiref` / `tensorSum`: 所有 xs shape 相同时正确。真实 multiref BW 应满足
- `bw_view`: 生成图零使用，理论 CONDITIONAL 依赖 params = 原 shape，未经真实检验
- `bw_add2`: 无广播时正确（GPT-2 all same-shape 满足）

### ⚠️ 真实 BUG — `bw_softmax` semantic mismatch

**Denote 定义**：
```lean
def softmaxBwd (g y : Tensor) : Tensor :=
  ...
    let dot := ∑ j, y[base+j] * g[base+j]
    y[base+idx] * (g[base+idx] - dot)
  ...
-- evalOp: BW_softmax [g, y] => [bw_softmax g y]
```
**Denote 假设第 2 arg = softmax output `y`**（PyTorch autograd 惯例）。

**但 GPT-2 生成图里**：
- FW_softmax `ins=[585]` outs=[586]  — 585 = softmax **input** (from FW_div=attn_scores), 586 = softmax **output** (attn_weights)
- BW_softmax `ins=[746, 585]` — **保存的是 585 (softmax input) 不是 586 (output)** ❌

**所有 20 处 BW_softmax，2nd input 都不在 FW_softmax outputs 集合里**：
- FW_softmax outputs: 20 个 tid（586, 621, ...）
- BW_softmax 2nd inputs: 20 个 tid（585, 620, ...）
- 交集：**0**
- 差值：**20** — 全部 mismatch

**结果**：Denote 用 `x·(g - Σ x·g)` 而不是 `y·(g - Σ y·g)`, 计算的是**根本不是任何合理 backward** 的表达式。

**Impact on GPT-2 proofs**：
- **Bridge 定理不受影响**（两侧都用同一个 broken Denote，internal-consistency 成立）
- **但 "Denote 语义 = PyTorch 语义" 的信任链彻底断裂**：GPT-2 的 312 桥证明的是"Denote's parallel BW_softmax = Denote's single BW_softmax"，**不是** "PyTorch's parallel BW_softmax = PyTorch's single BW_softmax"

### 修复选项

- **A. 修 Denote.bw_softmax**：让它假设第 2 arg = input x，内部重算 `softmax(x)` 得到 y，再算 backward。数学上正确但慢（每次 backward 都重新 softmax）。
- **B. 修 nnscaler 生成图**：让 BW_softmax 的 saved_tensor 是 output 586 而不是 input 585。**这是 nnscaler 图生成器的事，不是我能改的**。
- **C. 澄清 Denote 的 evalOp binding**：可能 nnscaler 实际约定"BW_softmax 存 input，Denote 内部要 recompute"，如果是这样，Denote 的 `bw_softmax` 定义就是错的（应该 recompute）。

---

## Pattern_2 / 4 / 5 audit

- **L1** ✅ (fixed-arity, no `::` reorder)
- **L2** ✅ (fw_embedding, fw_topk_routing, fw_inner_chunk_ce, fw_stack all semantically correct)
- **L3** ✅ (`prove_pattern_2/4/5` 各自只依赖 5-axiom kernel)

**Same caveat**: 若这些 op 的 Denote 定义 semantically wrong 对 PyTorch，bridges internal-consistent 但外部信任链断了。

---

## Pattern_1 audit

- **L1** ❌ `FW/BW × maybe_(un)shuffle` — evalOp binding `cu :: xs` assumes cu at ins[0], graph puts data at ins[0]
- **L2** ❌ `fw_maybe_(un)shuffle` uses `xs.head?.shape` as firstShape → all outputs shape [2] not data shape
- **L3** ❌ `prove_pattern_1` depends on `fw_maybe_unshuffle_cp2_commute` which is provably inconsistent

---

## 综合结论 (revised)

**GPT-2 的 312 桥证明**：
- **技术上有效**（L3 clean）✅
- **数学上 self-consistent**（Denote 内部一致）✅
- **但 Denote 语义 vs PyTorch 语义有 1 个真实 mismatch (`bw_softmax`)** — 这让 "GPT-2 parallel training is correct" 的自然语言解读**不严格对应 PyTorch 真实行为**

**要修**：
1. 决定 `bw_softmax` 该如何 fix（选 A/B/C）
2. Pattern_1 需要完全重做 (Denote def + evalOp + 重证)
3. 或者接受"Denote 是 nnscaler 的形式化，跟 PyTorch 主分支可能有差异" — 定义什么算 authority

---

## Layer 1 summary (Denote.lean 149 arms)

- 4 op families (FW/BW × maybe_(un)shuffle) use `::` pattern → L1 ❌
- 65 其他 ops fixed-arity → L1 ✅
