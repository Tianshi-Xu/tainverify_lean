# Denote Op Semantics Audit — 2026-07-03 (v4, softmaxBwd fix WIP)

## Status snapshot (2026-07-03, 6ffb70bxx build)

### GPT-2 ly4 (312 桥)
- **L1**: ✅ (26 non-collective + 4 collective ops, all fixed-arity patterns)
- **L3**: ✅ (`gpt_main_all_goals` depends only on 5-axiom kernel)
- **L2 issues found**:
  - ⚠️ **`softmaxBwd` semantic mismatch**: Denote assumes 2nd arg = softmax output y (docstring says `dx_i = y_i * (g_i - Σ y_j*g_j)`), but nnscaler graphs pass softmax INPUT x (from FW_div, not FW_softmax outputs). 20/20 GPT-2 BW_softmax nodes exhibit this pattern.
  - Others verified or CONDITIONAL on premises GPT-2 satisfies (see v3).

### Pattern_2 / Pattern_4 / Pattern_5 (MoE yoco_goals)
- **L1** ✅ **L3** ✅ **L2**: main ops verified

### Pattern_1 (MoE + CP)
- **L1** ❌ **L2** ❌ **L3** ❌ VACUOUS (fw_maybe_unshuffle_cp2_commute inconsistent)

---

## softmaxBwd fix — WIP status

**Attempted fix** (commits `cc34190`, `31e6135` context):

Approach: rename old `softmaxBwd g y` → `softmaxBwdFromOutput g y` (unchanged code, honest name); introduce new `softmaxBwd g x = softmaxBwdFromOutput g (softmax x)` that matches nnscaler convention; keep `bw_softmax := softmaxBwd`.

Result: **Build broke at 7 sites** (5 auxiliary lemmas + 2 direct uses). All 4 downstream
bridges (Goal_129/164/199/234) would need re-proof under the new semantics because:

- Auxiliary lemmas assert `softmaxBwd g y = <formula involving valAt y>` (was TRUE under old
  semantics; FALSE under new semantics where `softmaxBwd g y` internally computes with
  `softmax y`).
- Bridge tactic scripts unfold `softmaxBwd` then match old formula.

**Bridge theorems (equalities) themselves would remain TRUE** under the corrected semantics
because both LHS and RHS of the equality use `bw_softmax`, and softmax commutes with the
dim-2 gather. But the proofs need re-writing.

**Decision (2026-07-03)**: reverted the code fix — kept the old `softmaxBwd` (semantic
misnomer) with an explicit ⚠️ warning docstring pointing to `softmaxBwdFromInput` as the
canonical corrected form. `softmaxBwdFromInput g x = softmaxBwd g (softmax x)` is provided
as a companion definition for future refactors, but is NOT yet wired into evalOp.

**Full build passes (7746 jobs)** with warning docstring in place.

**Remaining work** to fully close this semantic gap: 4 bridges + ~6 aux lemmas
re-proof (estimated 10-20h focused work).

---

## Layer 1 detailed findings

Total OpName arms in Denote.lean: 149 (over 67 unique ops)
Total non-trivial `::` patterns: **8** (all in FW/BW × maybe_shuffle/unshuffle):
- `FW_maybe_shuffle`   L3729 evalOp `cu :: xs` + L3483 tp_shape `_cu :: x0 :: _rest` ❌
- `FW_maybe_unshuffle` L3733 evalOp `cu :: xs` + L3485 tp_shape `_cu :: x0 :: _rest` ❌
- `BW_maybe_shuffle`   L3737 evalOp `cu :: gs` + L3487 tp_shape `_cu :: g0 :: _rest` ❌
- `BW_maybe_unshuffle` L3741 evalOp `cu :: gs` + L3489 tp_shape `_cu :: g0 :: _rest` ❌

All other 61 ops use fixed-arity destructuring (`[x]`, `[x, y]`, `[x, w]`, `[g, x, w]`, `[x, weight, bias]`, `[ids, weight]`, `xs`, etc.). No arg-order ambiguity → L1 clean.

## Layer 2 findings (from subagent audit + Iroha spot-checks)

### VERIFIED (semantics match Python for target usage)

- `fw_sum` / `bw_sum` (shape `[1]` differs from PyTorch `()` cosmetically)
- `fw_gelu` / `bw_gelu` — exact GELU (matches nanogpt fixture using `F.gelu` default)
- `fw_linear` / `bw_linear` — `y = x @ w.T`, 2D/3D only
- `fw_matmul` / `bw_matmul` — batch strict alignment required, GPT-2 satisfies
- `fw_softmax` — standard softmax (VERIFIED)
- `fw_multiref` — `List.replicate n x`
- `fw_contiguous` / `bw_contiguous` — identity (correct)
- `fw_transpose` / `bw_transpose` — swap dims (correct)
- `fw_view` — numel-preserving reshape (GPT-2 always numel-preserving)
- `fw_layernorm` / `bw_layernorm` — single-last-dim normalization, eps=1e-5 hardcoded (matches typical usage)
- `fw_embedding` / `bw_embedding` — weight[ids] lookup
- `fw_topk_routing` / `fw_inner_chunk_ce` / `fw_stack` (Pattern_2/4/5) — verified

### CONDITIONAL

- `elemwiseAdd/elemwiseMul` — `outShape2` only picks longer-length shape; NOT full PyTorch
  broadcasting. GPT-2 all same-shape, satisfies. Pattern_1 uses broadcast → mismatch there.
- `fw_div/bw_div` — divisor restricted to `Nat` (can't express `1/√d_k`). GPT-2 uses `params=[2]`, satisfies.
- `bw_add2` — needs `g.shape` = true broadcast shape. Same-shape case verified.
- `bw_multiref` / `tensorSum` — assumes all input shapes same (holds for typical multiref BW).
- `bw_view` — 0 usage in generated graphs, statement structurally correct but unchecked.

### ⚠️ SEMANTIC MISMATCH

- `softmaxBwd` (aka `bw_softmax`) — Denote assumes 2nd arg = softmax OUTPUT y;
  nnscaler graphs pass INPUT x. **See "softmaxBwd fix WIP" section above.**

### BROKEN (Pattern_1 only)

- `fw_maybe_shuffle` / `fw_maybe_unshuffle` (and BW_ variants) — evalOp binds `cu :: xs` but
  graph puts data at ins[0], cu_seqlens at ins[1]. Also `firstShape := xs.head?.shape` uses
  metadata not data.

---

## Recommended path forward

1. **Short term**: `softmaxBwd` semantic warning documented in code. Full build passes.
   Pattern_2/4/5 & GPT-2 bridges technically valid (internal consistency).
2. **Medium term**: Fix `softmaxBwd` semantics + re-prove 4 bridges (~10-20h). This closes
   the softmax layer's PyTorch alignment gap.
3. **Long term**: Pattern_1 requires:
   - Fix Denote `fw_maybe_(un)shuffle` def to use data (ins[0]) not cu (ins[1]) for shape;
   - Fix evalOp binding accordingly;
   - Rewrite Pattern_1's 200-line proof (previous proof was VACUOUS due to inconsistent axiom).

Estimated total effort: 30-60h.


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
