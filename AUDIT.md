# Denote Op Semantics Audit — 2026-07-03 (v5, softmaxBwd fix COMPLETED)

## Status snapshot (2026-07-03, commit e11b68f on branch fix-g164)

### GPT-2 ly4 (312 桥)
- **L1**: ✅ (26 non-collective + 4 collective ops, all fixed-arity patterns)
- **L2**: ✅ (softmaxBwd fix applied, matches nnscaler graph convention)
- **L3**: ✅ pending final verification (`#print axioms gpt_main_all_goals` after
  full bridge build completes; expected to still be 5-axiom kernel + native_decide)

### softmaxBwd fix — COMPLETED (branch fix-g164, commit e11b68f)

**Semantic fix**:
- `softmaxBwd g x := softmaxBwdFromOutput g (softmax x)` — matches nnscaler convention
  (BW nodes save FW input, not FW output)
- `softmaxBwdFromOutput g y = y_i * (g_i - Σ_j y_j g_j)` — the pure form assuming
  y = softmax output (was the old `softmaxBwd` body, renamed for honesty)
- `bw_softmax := softmaxBwd` (unchanged abbrev; used by evalOp)

**Refactor applied uniformly to g129/g164/g199/g234 chains**:

1. All 6 aux lemmas renamed `softmaxBwd_XXX_gYYY → softmaxBwdFromOutput_XXX_gYYY`
   (their statements now correctly assert facts about `softmaxBwdFromOutput` on
   softmax output tensors — TRUE under new semantics; no proof body change).

2. Distributive lemmas renamed similarly:
   - `bw_softmax_distribute_allGatherPrimDimN_dim2_4_1_4_2_8_g164`
     → `softmaxBwdFromOutput_distribute_allGatherPrimDimN_dim2_4_1_4_2_8_g164`
   - `bw_softmax_allGatherPrimDimN_2_4_eq_g129`
     → `softmaxBwdFromOutput_allGatherPrimDimN_2_4_eq_g129`
   - `bw_softmax_split_dim2_4_1_4_8_8_g199`
     → `softmaxBwdFromOutput_split_dim2_4_1_4_8_8_g199`
   - `softmaxBwd_split_dim1_4_1_4_8_8_g234`
     → `softmaxBwdFromOutput_split_dim1_4_1_4_8_8_g234`
   (and their piece/valAt/unfold helpers)

3. Added new **softmax_chunkPrimDimN commute helpers**:
   - `softmax_chunkPrimDimN_dim2_1_4_8_8_g199` (softmax commutes with dim-2 chunk)
   - `softmax_chunkPrimDimN_dim1_1_4_8_8_g234` (softmax commutes with dim-1 chunk)

4. Added new **top-level wrappers with SAME NAME** as before:
   - `bw_softmax_distribute_allGatherPrimDimN_dim2_4_1_4_2_8_g164`
   - `bw_softmax_allGatherPrimDimN_2_4_eq_g129`
   - `bw_softmax_split_dim2_4_1_4_8_8_g199`
   - `softmaxBwd_split_dim1_4_1_4_8_8_g234`
   These compose softmax_allGather/chunk with the renamed FromOutput distributive
   lemmas. Bridge files `Goal_129/164/199/234.lean` reference these wrappers by
   their unchanged names.

5. Added shape compat wrappers (needed by Goal_164 and Goal_234):
   - `bw_softmax_shape_1_4_8_8_g164`
   - `bw_softmax_shape_1_4_2_8_g164`
   - `bw_softmax_shape_d8_g234`

6. Updated `Goal_164.lean` and `Goal_234.lean` to reference:
   - shape lemmas via `bw_softmax_shape_*` (new wrappers)
   - eq_mkShape / valAt lemmas via `softmaxBwdFromOutput_*` (renamed pure-form)

**Verification**:
- `denote.Denote` builds ✓
- Full `lake build` (7746 jobs) passes ✓
- `denote.gpt_ly4_regen.MainTheorem` build in progress at time of commit
  (3083/3254 built, 0 errors so far). Deferred verification of complete bridge
  compilation + `#print axioms gpt_main_all_goals` still yielding 5-axiom kernel.

---

### Pattern_2 / Pattern_4 / Pattern_5 (MoE yoco_goals)
- **L1** ✅ **L3** ✅ **L2**: main ops verified. Independent of softmaxBwd change.

### Pattern_1 (MoE + CP)
- **L1** ❌ **L2** ❌ **L3** ❌ VACUOUS (fw_maybe_unshuffle_cp2_commute inconsistent)
- **NOT ADDRESSED** by this fix — Pattern_1's issues are separate (fw_maybe_unshuffle
  binding bug + inconsistent axiom). Deferred.

---

## Layer 1 detailed findings

(unchanged from v4)

Total OpName arms in Denote.lean: 149 (over 67 unique ops)
Total non-trivial `::` patterns: **8** (all in FW/BW × maybe_shuffle/unshuffle):
- `FW_maybe_shuffle`   L3729 evalOp `cu :: xs` + L3483 tp_shape `_cu :: x0 :: _rest` ❌
- `FW_maybe_unshuffle` L3733 evalOp `cu :: xs` + L3485 tp_shape `_cu :: x0 :: _rest` ❌
- `BW_maybe_shuffle`   L3737 evalOp `cu :: gs` + L3487 tp_shape `_cu :: g0 :: _rest` ❌
- `BW_maybe_unshuffle` L3741 evalOp `cu :: gs` + L3489 tp_shape `_cu :: g0 :: _rest` ❌

All other 61 ops use fixed-arity destructuring. No arg-order ambiguity → L1 clean.

## Layer 2 findings (from subagent audit + Iroha spot-checks)

### VERIFIED (semantics match Python for target usage)

- `fw_sum` / `bw_sum` (shape `[1]` differs from PyTorch `()` cosmetically)
- `fw_gelu` / `bw_gelu` — exact GELU (matches nanogpt fixture using `F.gelu` default)
- `fw_linear` / `bw_linear` — `y = x @ w.T`, 2D/3D only
- `fw_matmul` / `bw_matmul` — batch strict alignment required, GPT-2 satisfies
- `fw_softmax` — standard softmax (VERIFIED)
- **`fw_softmax` / `bw_softmax`** — NOW matches nnscaler graph convention ✓
  (bw_softmax accepts FW input x, recomputes softmax internally)
- `fw_multiref` — `List.replicate n x`
- `fw_contiguous` / `bw_contiguous` — identity (correct)
- `fw_transpose` / `bw_transpose` — swap dims (correct)
- `fw_view` — numel-preserving reshape (GPT-2 always numel-preserving)
- `fw_layernorm` / `bw_layernorm` — single-last-dim normalization, eps=1e-5 hardcoded
- `fw_embedding` / `bw_embedding` — weight[ids] lookup
- `fw_topk_routing` / `fw_inner_chunk_ce` / `fw_stack` (Pattern_2/4/5) — verified

### CONDITIONAL (still)

- `elemwiseAdd/elemwiseMul` — `outShape2` only picks longer-length shape (GPT-2 all
  same-shape; Pattern_1 uses broadcast so mismatch there)
- `fw_div/bw_div` — divisor restricted to `Nat` (GPT-2 uses `params=[2]`, satisfies)
- `bw_add2` — needs `g.shape` = true broadcast shape (same-shape case verified)
- `bw_multiref` / `tensorSum` — assumes all input shapes same (holds for typical usage)
- `bw_view` — 0 usage in generated graphs, structurally correct but unchecked

### BROKEN (Pattern_1 only, unchanged)

- `fw_maybe_shuffle` / `fw_maybe_unshuffle` (and BW_ variants) — evalOp binds
  `cu :: xs` but graph puts data at ins[0], cu_seqlens at ins[1]. Also
  `firstShape := xs.head?.shape` uses metadata not data.

---

## Recommended path forward

1. **Short term (this session)**: verify `denote.gpt_ly4_regen.MainTheorem` builds cleanly
   AND `#print axioms gpt_main_all_goals` still yields 5-axiom kernel.
2. **Merge `fix-g164` into `work-from-main-2026-06-12`** after (1).
3. **Long term**: Pattern_1 fix (fw_maybe_unshuffle bug) requires:
   - Fix Denote `fw_maybe_(un)shuffle` def to use data (ins[0]) not cu (ins[1]) for shape;
   - Fix evalOp binding accordingly;
   - Rewrite Pattern_1's 200-line proof (previous proof was VACUOUS due to inconsistent axiom).

Estimated total effort for Pattern_1: 20-40h.

## New lessons learned (added to AGENTS.md)

- **Lesson 21**: subagents don't auto-isolate via git worktree — must `git worktree add` per branch before dispatching if they'll edit shared files
- **Lesson 22**: subagent iteration budget (~45 tool calls) too small for complex Lean proof surgery — decompose into <30-call atomic tasks or do serially
- **Lesson 23**: Lean `/-- ... -/` docstring cannot be followed by `set_option ... in`; use `-- ...` line comments instead in that context



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
