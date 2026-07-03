# TrainVerify Bridge Emitter — Build-Time Optimization Plan

**Goal:** 把 312-goal full build 时间从 ~2h 降到目标 ≤ 45min（YOCO 未来 1000+ goal 才能可扩展）。

**Architecture:** 攻击 `native_decide` 密度（当前主要 cost），复用 handwritten g3 里 `pm_prefix_eq` / `sm_prefix_eq` 一次证明多次用的思路，减少每个 `pm_val` / `sm_val` 生成的独立 `native_decide` 数量。

**Tech Stack:** Python emitter (`renderer.py` / `renderer_uni.py`), Lean 4 (v4.27.0-rc1), lake build.

---

## 侦察数据（2026-07-01）

单文件 clean-build timing:

| Goal | Time | native_decide 数 | 备注 |
|------|------|-----------------|------|
| g3   | **63s** | 10 | Handwritten, 用 `denoteGraph_tid_eq_of_forall_not_mem_outs` 一次 decide 整个 pm.nodes |
| g10  | 5s  | 41 | Auto-gen, 小 goal (prereqs=[2..9]) |
| g100 | **139s** | 32 | Auto-gen, 大 goal (prereqs 130+) |
| g110 | ~60-90s | **108** | Auto-gen, `native_decide` 密度冠军 |

**关键洞察（推翻上次判断）：**
1. Handwritten g3 **反而更慢**（63s），"斩后缀"路径需要对整个 pm.nodes 做一次 `native_decide`（O(N)），而 `pm_val` 只需对 `pm.nodes.drop (k+1)` 做（O(N-k)）
2. `pm_val` 在 BridgeKit 内部**已经封装了** `denoteGraph_tid_eq_of_suffix_no_writes` —— 策略上和 g3 handwritten 等价
3. 真正的 cost 在**每个 `pm_val` / `sm_val` / `pm_prefix_eq` 都独立跑一次 `native_decide`**：g110 有 108 个 → 108 次 kernel 展开
4. handwritten g3 的智慧不是"高层引理"，是**把多个 tid 的 `native_decide` 合并成一个** `hno : ∀ n ∈ pm.nodes.drop 9, (1089 : Tid) ∉ n.outs`（一个 decide 服务 4 个 tp_frame）

**优化空间估算：** 如果 g100/g110 类大 goal 能砍 50% native_decide，全 build 从 2h → 1h。目标做到 45min 需要另加 hInitCut helper 优化 + 并行 lake job。

---

## Current context / assumptions

- 子鱼放宽了 build 限制，可以局部 build 验证
- 目前 227/311 PASS_EXACT 是安全 baseline（已 commit 73f5fe0，本地）
- 5 个 autogen DIFF (g65/104/242/250/312) 是 semantic-equivalent 差异，不 block 优化实验
- 77 handwritten DIFF (g3-g64 range) — 上次分析证明大多是 cosmetic 差异，本 plan 不动它们

## Proposed approach

**分 3 阶段，每阶段独立 benchmark：**

- **Phase A — Batched hdrop lemma**：把同一 `pm_frame_*_self` 系列的多个独立 `by native_decide` 合并成一个 shared `hdrop_g<n>_tp<tid>` lemma；同理 SM 侧
- **Phase B — Cache node-structure lemma**：`rw [show pm.nodes[k]'... = { ... } from by native_decide]` 每个 tid 都跑一次，改成 `pm_node_k` cached lemma
- **Phase C — Assembly hInitCut 优化**：`goal_N_hInitCut_helper` 里的 `simp only [List.forall_mem_append, ...]` 是 O(prereqs^2) 的 —— 用 `List.forall_mem_cons` chain 展开成显式 term-mode

**每阶段：先在 g100 / g110 上验证，再全 build 对比 total time。**

## Step-by-step plan

### Phase A: Batched hdrop lemma (核心优化)

**当前 emit 输出 (示例 pm_full_g3_1085 line 44-53)：**
```lean
theorem pm_full_g3_1085 (initPM : Store) :
    denoteGraph pm initPM 1085
      = chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 716) := by
  rw [pm_val initPM 1 1085 (by native_decide) (by native_decide)]  -- 2 next
  rw [show pm.nodes[1]'(by native_decide) = {...} from by native_decide]  -- 2 next
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 1 716 (by native_decide)]  -- 1 native_decide
```

**每个 pm_full_g<n>_<mid> 有 5 个 `native_decide`**。g100 里 `pm_full_g100_XXX` 有 ~16 个 mid tensor → 80 次 native_decide 就是这批。

**优化方案：** 加入 `BridgeKit` 一批 batched lemma，然后 emitter 输出改为引用它们。

#### Task A1: 加 `hdrop_below_shape` batched proof kit (BridgeKit.lean)

**Objective:** 在 BridgeKit 里加一个 helper，把"pm.nodes.drop (k+1) 里所有 node.outs 都不含 tid" 的证明工厂化。

**Files:**
- Modify: `trainverify/denote/gpt_ly4_regen/BridgeKit.lean`

**Step 1:** 在 BridgeKit 末尾（line 96 之前 `end` 之前）追加：

```lean
-- Batched hdrop wrapper: cache the (∀ n ∈ pm.nodes.drop (k+1), tid ∉ n.outs)
-- proof so multiple pm_val/pm_prefix_eq call sites for same (k, tid) share one
-- native_decide. Downstream generated goal bridges instantiate this per (k, tid).
--
-- NOTE: This is a proof-shape helper, not a new theorem — callers pass their own
-- (k, tid, hk) inline. The purpose is to give emitter a naming target so a single
-- `have h_drop_pm_k_tid : ...` at the top of a proof block can be reused.
```

**Step 2:** 用 patch 添加 lemma:

```lean
theorem pm_val_of_hdrop (initPM : Store) (k : Nat) (out : Tid) (hk : k < pm.nodes.length)
    (hdrop : ∀ n ∈ pm.nodes.drop (k+1), out ∉ n.outs) :
    denoteGraph pm initPM out
      = applyNode pm (denoteGraph {pm with nodes := pm.nodes.take k} initPM) pm.nodes[k] out :=
  pm_val initPM k out hk hdrop

theorem sm_val_of_hdrop (initSM : Store) (k : Nat) (out : Tid) (hk : k < sm.nodes.length)
    (hdrop : ∀ n ∈ sm.nodes.drop (k+1), out ∉ n.outs) :
    denoteGraph sm initSM out
      = applyNode sm (denoteGraph { sm with nodes := sm.nodes.take k } initSM) sm.nodes[k] out :=
  sm_val initSM k out hk hdrop
```

（暂时先只加 wrapper 为了不改核心 lemma 签名。后续可以直接改 emitter 输出跳过 wrapper。）

**Step 3:** verify:
```bash
cd ~/.openclaw/workspace/tainverify_lean/trainverify
lake build denote.gpt_ly4_regen.BridgeKit
```
Expected: EXIT 0, olean built.

#### Task A2: 改 renderer.py `pm_frame_block` 输出 shared hdrop

**Objective:** 把 pm_frame_*_self 系列证明改成"顶部一个 hdrop → 复用给 pm_val + pm_prefix_eq"

**Files:**
- Modify: `trainverify/bridge_emitter/renderer.py` (function around line 130 `pm_frame_block`)

**Current renderer template (line 130-138):**
```python
f"""theorem pm_frame_{tp_tid}_self (initPM : Store) :
    denoteGraph pm initPM {tp_tid}
      = {op_call_store(sm_op, pm_node_ins, "denoteGraph pm initPM")} := by
  rw [pm_val initPM {pm_node_idx} {tp_tid} (by native_decide) (by native_decide)]
  rw [show pm.nodes[{pm_node_idx}]'(by native_decide)
      = {{ rank := {tp_rank}, op := "OpName.{sm_op}", ins := [{ins_str}], outs := [{tp_tid}] }}
      from by native_decide]
  rw [{helper}]
  rw [{prefix_rws}]
```

**New template — factor common decides:**
```python
f"""theorem pm_frame_{tp_tid}_self (initPM : Store) :
    denoteGraph pm initPM {tp_tid}
      = {op_call_store(sm_op, pm_node_ins, "denoteGraph pm initPM")} := by
  have hk : {pm_node_idx} < pm.nodes.length := by native_decide  -- 1×
  have hdrop : ∀ n ∈ pm.nodes.drop ({pm_node_idx}+1), {tp_tid} ∉ n.outs := by native_decide  -- 1×
  have hnode : pm.nodes[{pm_node_idx}]'hk
      = {{ rank := {tp_rank}, op := "OpName.{sm_op}", ins := [{ins_str}], outs := [{tp_tid}] }} := by
    native_decide  -- 1×
  rw [pm_val initPM {pm_node_idx} {tp_tid} hk hdrop, hnode, {helper}, {prefix_rws_inline}]
```

**每个 pm_frame_*_self**：3 个 native_decide → 3 个（同数量）**但每个都独立命名**，Lean 会 cache decl 结果。

**关键收益：** `pm_prefix_eq initPM {pm_node_idx} {input_tid} (by native_decide)` 的 `by native_decide` 是**独立**跑的 —— 但如果 `pm_node_idx` 同一个，`pm.nodes.drop {pm_node_idx}` 已经通过 `hdrop` cache 过。这里需要 `pm_prefix_eq` 输入不同 tid 时**能否复用 same k 的 hdrop**——不能直接，因为 tid 不同。**Phase A 单点优化收益有限，需要 Phase B/C 配合**。

Actually 上面 template 收益不明显。让我先 spike 一个真收益的 idea：

#### Task A3: SPIKE - single-goal micro-benchmark

在动 renderer 前，先手动改写 `Goal110Bridge.lean`（native_decide 密度冠军）里 3-5 个 pm_frame 用不同 tactics，测每种能省多少时间。

**Approach:**
- Baseline (current): 108 native_decide, 单 file build 时间
- Variant 1: 把 `by native_decide` 内联全部替换为 `by decide` 看是否一样快
- Variant 2: hoist shared `hnode_k` (对同一 k 的 node 结构缓存)
- Variant 3: 换 `rfl` （如果 def-eq 成立）

**Files:**
- Create: `.hermes/plans/spikes/goal110_bench/` (workspace for spike copies)

**Step 1:** copy Goal110Bridge.lean 到 3 个变体
```bash
cd ~/.openclaw/workspace/tainverify_lean/trainverify
mkdir -p /tmp/g110_spike
cp denote/gpt_ly4_regen/Goal110Bridge.lean /tmp/g110_spike/Goal110Bridge_v0.lean
# 变体见 Task A3-v1/v2/v3
```

**Step 2:** 每个变体独立 clean-build + time
```bash
for v in v0 v1 v2 v3; do
  cp /tmp/g110_spike/Goal110Bridge_${v}.lean denote/gpt_ly4_regen/Goal110Bridge.lean
  rm -f .lake/build/lib/lean/denote/gpt_ly4_regen/Goal110Bridge.olean
  time lake build denote.gpt_ly4_regen.Goal110Bridge
done
# Restore original
cp /tmp/g110_spike/Goal110Bridge_v0.lean denote/gpt_ly4_regen/Goal110Bridge.lean
```

**Expected:** 拿到 v0 vs v1/v2/v3 具体秒数差，决定哪种优化真值得推 emitter。

**Step 3:** 记录结果到 `iroha-tasks/trainverify-bw/spike-benchmark.md`

### Phase B: Cache node-structure lemma

**观察：** 每个 `rw [show pm.nodes[{k}]'(...) = { rank, op, ins, outs } from by native_decide]` 里 `by native_decide` 展开的是**同一个 GraphDecl 的 nodes[k]**。如果 goal_N 里有多个 pm_frame 都引用 `pm.nodes[k]`（大概不会重叠），或引用相邻 k（共享 `pm.nodes` 展开）也许可以共用。

**这个 Phase 依赖 A3 的实验结果 —— 如果 A3 显示 node-decode `native_decide` 是大头，就走 B；否则 skip**。

### Phase C: hInitCut 优化

**当前 renderer.py line 172-184：**
```lean
lemma goal_{n}_hInitCut_helper (Ssm Spm : Store) (hinitC ...) (hg2 ...) (hg3 ...) ... :
    InitGoalsHold pm_goal_{n}.numRanks goal_{n}_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_{n}.numRanks = pm.numRanks := by native_decide
  rw [hnr]
  simp only [InitGoalsHold] at hinitC ⊢
  simp only [goal_{n}_cut_initGoals, goal_{n}_prereqs, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨hinitC, hg2, hg3, ..., List.forall_mem_nil _⟩
```

**问题：** `simp only [goal_{n}_cut_initGoals, goal_{n}_prereqs, ...]` 展开时如果 prereqs 有 130 个（g100 case），`goal_{n}_prereqs` 定义就是 130-element list，simp 需要展开成 130 个 `forall_mem_cons`。O(n) per goal，全 build O(sum n) = O(N²) total。

**优化：** 改用 direct term mode 构造，绕过 simp:

```lean
lemma goal_{n}_hInitCut_helper (Ssm Spm) (hinitC ...) (hg2 ...) ...  :
    InitGoalsHold pm_goal_{n}.numRanks goal_{n}_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_{n}.numRanks = pm.numRanks := by native_decide
  intro g hg
  -- g 一定是 goal_N_cut_initGoals 的成员，展开成初始 + prereqs 的成员
  rcases List.mem_append.mp (by rw [show goal_{n}_cut_initGoals = initGoals ++ goal_{n}_prereqs from rfl] at hg; exact hg) with hg_init | hg_prereq
  · exact hinitC g hg_init
  · -- 对 g ∈ goal_{n}_prereqs 逐个 dispatch 到 hg_m
    ...
```

这个 idea 需要先验证 `goal_{n}_cut_initGoals` 定义确实是 `initGoals ++ goal_{n}_prereqs`。如果是，term-mode 版本可以是 O(1) per instantiation。

**注意：** renderer 注释里已写"O(n^2) rcases → O(n) simp"，说明之前踩过坑。**不能盲目回到 rcases**。Phase C 需要仔细验证。

## Files likely to change

- `trainverify/denote/gpt_ly4_regen/BridgeKit.lean` (可能加 batched wrappers)
- `trainverify/bridge_emitter/renderer.py` (核心 template 改)
- `trainverify/bridge_emitter/renderer_uni.py` (universal renderer 同步)
- **Regenerate all auto-gen bridges** after emitter change：`python3 bridge_emitter/emit2.py <n> --out denote/gpt_ly4_regen/Goal<n>Bridge.lean` for n in autogen goals

## Tests / validation

**Per-phase check：**
```bash
cd ~/.openclaw/workspace/tainverify_lean/trainverify
# 单文件验证 emitter 改后 lint OK
python3 bridge_emitter/emit2.py 110 --no-compile --out /tmp/g110_new.lean

# 局部 build 验证证明还过
rm -f .lake/build/lib/lean/denote/gpt_ly4_regen/Goal110Bridge.olean
time lake build denote.gpt_ly4_regen.Goal110Bridge
```

**Cumulative check:**
```bash
# 全 build 计时（baseline 大概 2h）
time lake build 2>&1 | tail -5
```

**Regression check:**
- Axiom check 必须仍然 clean（无新 sorry）
- 全 build EXIT 0
- MainTheorem 0 sorry

## Risks, tradeoffs, open questions

**Risk 1: `native_decide` 内部到底慢在哪不确定。** 可能是 `pm.nodes.drop k` 里的 List.drop 计算（需要展开 List cons N 次），也可能是 `n.outs` membership check（tid 是 Nat，Nat 比较是快的）。**A3 spike 是关键**——先不动 renderer，先测清楚每一次 native_decide 用掉多少 ms。

**Risk 2: Handwritten g3 那种"合并 hdrop"思路** 在小 pm.nodes (base case) 快，但 pm.nodes 变大（312+ nodes）时 `∀ n ∈ pm.nodes.drop k` 的一次 decide 可能比多个 `∀ n ∈ pm.nodes.drop (k'+1)` 加起来更慢。要 benchmark 验证。

**Risk 3: 改 renderer 后 regenerate 所有 bridges 会引起大 diff，容易 introduce bug。** Mitigation: **每次改一个小 template，先只重生成 5-10 个 goal 验证 build 通，再全面 regen。**

**Open question 1: 并行 build 能省多少？** lake 默认单进程 sequential build，但机器 96 cores 大量空转。是否可以：
- 加 `-j 32` (lake 支持吗？) → **需要试**
- 或改用 `parallel :::` 拆多个独立 goal 一起 build（需自己写 script）

**Open question 2: 是否值得引入 `Decidable` instance 加速 `native_decide`？** 比如给 `pm.nodes.drop k` 的 outs check 写自定义 Decidable，可能比通用 whnf 展开快。**需要 Lean 4 内核知识确认**。

**Open question 3: 完全脱离 native_decide 走 lookup table 可行吗？** 生成时 emitter 已经知道每个 (k, tid) 是否 hdrop，能否直接 emit 一个 `#[false, false, ..., true, ...]` array + `Array.get` lookup lemma？——这是**极端优化**，最后手段。

---

## Suggested execution order

1. **首先做 Task A3 spike** — 拿到 native_decide 每次真实成本，决定 A/B/C 三个方向哪个先做
2. 根据 A3 结果，挑最大收益的 phase 展开
3. 每 phase 完成后跑全 build 计时对比 baseline (2h)
4. 目标里程碑：**Phase 1 完成后 → 90min, Phase 2 → 60min, Phase 3 → 45min**

**上限估算**：如果 native_decide 是**不可撼动**的 bottleneck，那纯 emitter 优化天花板可能只有 30% (2h → 84min)。真要突破 45min 必须并行化 build 或换 kernel 策略。

## Remember

- 每个 phase 完成后 **commit + push 一次** (子鱼要 review)
- 不动 handwritten g3-g30 那 30 个 bridge（除非验证 emitter 输出真的比它们快）
- **不要为了 PASS_EXACT 覆盖率去 flatten handwritten** —— 目标是 build time，不是文件一致性
