1.能直接引用的lemma千万不要用simp，否则编译速度会非常慢。
2.证明过程中不要中断询问用户意见。
3.实际上"lake build module.File"比"lake env lean"更快，因为有增量缓存。
4.新添加的引理必须放在它依赖的引理之后，否则会报"Unknown identifier"错误。
5.三元组目标（A ∧ B ∧ C）用`refine ⟨?_, ?_, ?_⟩`分解，而不是用`constructor`（只能分两部分）。
6.rewrite时注意顺序：先用`rw [hpm_list]`将PM侧重写为期望形式，再用`rw [← hbw]`应用主引理。
7.dW（权重梯度）和dX（输入梯度）的分布式计算引理是不同的，需要分别证明。
8.`simpa [def] using h`会展开定义，可能导致超时；改用`have h' := h; simp at h'; exact h'`。
9.`rw [h1] at h2`改写假设后，后续使用h2时表达式已变，不要再用原始形式。
10.Shape证明中，`bw_linear_snd_shape'`需要存在性witness，用`⟨a, b, proof⟩`构造。
11.不要写入tmp，没有权限。
12.`fin_cases hn <;> decide` 在 list ≥ 50 元素时超 heartbeats（O(n²)）；改用 `native_decide`（加 5-axiom baseline `Lean.ofReduceBool + Lean.trustCompiler`）。
13.rw chain 引入嵌套 `List.map s L` 时，每一层需要单独 `simp only [List.map]` 展开才能后续 rw 匹配。例：多层 fold + fw_stack 组合，分 3 段 `simp only [List.map]; rw [...]`。
14.`congr 1 <;> tactic` 会尝试关闭已关的 goal 报 "No goals to be solved"；改用 `show + have + 显式 rw` 更可控。
15.`fw_maybe_unshuffle` 参数顺序反直觉：graph 里 `ins=[data_tid, cu_tid]`，evalOp `cu :: xs` binding 让第一个位置叫 cu 但实际 fw_maybe_unshuffle 的第一个 arg 才是 data，xs (剩下) 是 cu_seqlens metadata。写 axiom 按实际调用顺序。
16.Weight tensor 也可能被 shard（如 MoE per-expert weight `[64, ..., ...]` PM里[32, ..] × 2）。不是所有 initGoal 都是 singleton — 检查 tps 长度决定用 extract_singleton 还是 extract_dual。
17.rw 里的 `zLossScale := 0` 不匹配 target 里的 `↑0`：需要 `zLossScale := ((0 : Nat) : Scalar)` 显式指定 Nat→Scalar coercion。
18.extract_dual 需要 shape witness 处理 reconstructWithDim 的 `if sh = [1] then allReduce else allGather`：simp with `hshape, if_neg hne` 关掉 if 分支。
19.生成 25+ 节点 machinery lemma：用 Python 脚本自动生成 per-tid 归约的 haves（Boundary → foldl_applyNode_at_not_written + fin_cases <;> decide; Written → split-take + applyNode_XXX_out helper; Fast-forward → foldl_take_split_at_not_written）。最终 rw 链末尾可能需要 `rfl` 处理 numeric normalization（如 `[k].getD 1 0 = 0`）。
20.**Axiom audit 强制**（2026-07-03 血教训）：每写完一个 sharding-commute axiom，立刻写 witness file 验证 LHS.shape = RHS.shape（Denote 语义下）。如果 shape 不等，axiom 是 inconsistent，能推 False，导致所有依赖它的定理 vacuous。**Pattern_1 的 `fw_maybe_unshuffle_cp2_commute` 就是这个坑**（LHS.shape=[2] vs RHS.shape=[4] because Denote 用 xs.head?.shape 不是 data.shape）。参考 `UnshuffleInconsistent.lean` 的 witness 模板。**必须做完 audit 才能声称 Pattern 已证**。
21.**Subagent 并发不 auto-isolate**（2026-07-03 血教训）：`delegate_task` 分派的多个 subagent 共享同一 filesystem，如果要各自改同一文件必 race。**必须** 先 `git worktree add /tmp/tv-<taskId> <branch>` 分独立 branch 再 dispatch，goal 中明确指定 subagent 的 workdir 为 worktree。
22.**Subagent iteration budget（~45 tool calls）不够修复 Lean 证明**（2026-07-03 教训）：3 个 subagent 尝试修 softmaxBwd chain 全部 timeout / iterated to death without finishing。Lean 证明修复需要多轮 build-error-fix 循环。**长手工任务不 delegate，或切成 <30 tool call 的原子子任务**（比如只 "rename 3 处 identifier + build verify"）。
23.**Lean `/-- ... -/` docstring 不能后跟 `set_option ... in`**（2026-07-03 教训）：`set_option ... in` 只接受紧跟着的 declaration，不接受 docstring 作 gap。改用 `-- ...` line comment 或把 docstring 移到 `set_option ... in` 之后紧接 `theorem`。
24.**跨 rank op 用 identity 模型**（2026-07-03 pattern1-fix 教训）：如果一个 op 的真实语义需要观察其他 rank 的 tensor 值（比如 CP zigzag shuffle 需要看所有 rank 的输入才能算本 rank 的输出），但 Denote 的 per-rank evalOp 只能看 local store，就把它模型化成 `def op (data _cu ...) : Tensor := data`（在 data 上恒等）。这在 `cpSize=1` 时精确（匹配 Python 的 early-return branch），在 `cpSize>1` 时**shape-correct 但 value-lossy**。**这比给个错的非 identity 模型好**——错的模型（比如从 metadata 派生 output shape）会让 sharding-commute axiom 变 inconsistent，静默毒化整个 proof chain（Pattern_1 v5 vacuous 教训）。**文档里明确写 fidelity note**。
25.**上游忠实性优先，下游成功是假的**（2026-07-03 子鱼铁令）：Denote 层任何跟 Python authority 不符的语义 bug，**必须先修上游**，才能证下游。下游 pattern 证明再多，只要上游算子语义错了，全都是"vacuous over garbage"。规则：
    - 每加一个 Denote op / 修一个 Denote def 前：**先跟 Python source 对照** input shape / output shape / value semantics
    - 上游 audit 未过之前，下游 sharding-commute axiom 不允许当 "TODO" 遗留 — 遇到就立刻上溯查 Denote 是不是错了
    - 陷阱：`fw_all2all_moe_gmm` 的 `hModel = w2.shape.reverse.head?` 错取了 w2 的 last dim（512），应用 `input.shape.reverse.head?` 取 x 的 last dim（d_model=1024）匹配 Python
    - 教训：Pattern_1 我先证下游 chain shape + rms_norm commute，遇到 fw_add 才发现 outer_add 是 broadcast garbage，回头查才发现是 fw_all2all_moe_gmm hModel bug。**顺序反了**
26.**Python bulk regex replacement 在 Lean 证明里危险**（2026-07-04 血教训）：当一个函数改名 (`fw_all2all_moe_gmm` → `_full`) 需要 propagate 到 30+ 处调用时，**禁止用 python 一 shot 批量 regex**。理由：同一函数名在不同 context 可能对应**不同 signature**；regex 不区分 hgmm0 (pm_chain_shape, 新 `_full` 签名) vs hgmm0_local (prove_goal_1, 可能需要旧签名 per-rank single-shard)。Regex 边界很难写对 paren-nested / whitespace-variant 的 args。部分替换（函数名换了但参数没换）会成 illegal Lean, 触发大量 downstream failure。**正确做法**：手工分块 patch — 每次 patch 一个 lemma / clause，build 验证，再继续。Recovery: 踩坑立刻 `git checkout HEAD -- <file>` rollback 从最近稳定 commit 重来。
27.**Lean rewrite tactic 里 `try rw` 会被 simp 已提前 normalize 打乱**（2026-07-04 教训）：`have := lemma ...` + `simp only [Nat.zero_add, ...] at this` 会把 `0 + x` 简化成 `x`。接下来 `try rw [show (0 + x) = x ...]` 找不到 `0 + x` (silent fail 因为 `try`)。到 `exact this` 时 type mismatch: expected `... + (0 + x)`, have `... + x`。**Fix**: 反向 rw 把 `x` 还原为 `0 + x`：`rw [show x = 0 + x from (Nat.zero_add x).symm] at this`。或者 predict 到 simp 会不会归约相关 pattern，选择 whether 加 `Nat.zero_add` 到 simp set。
28.**`fw_all2all_moe_gmm_full_split_commute_2` 证明模式**（2026-07-04 新证 zero-sorry）：无 disjoint 假设的上游忠实 sharding-commute，pattern：Setup unfold `_full` → LHS 和 RHS 内层都是 `fw_all2all_moe_gmm on gathered w13/w2`（同一 tensor）。Tensor.ext + decompose outIdx 为 (r*L+i)*hM+col。`interval_cases r` 分 r=0/1。Apply `fw_all2all_moe_gmm_valAt` (LHS 用 lDim=L*2, RHS 用 lDim=L). Apply `allGatherPrimDimN0_valAt` 到 RHS 外层 allGather. `Finset.sum_congr rfl` + `moe_gmm_term_congr`: hmask/hprob/hinput via bridge, hw13/hw13'/hw2 = trivial rfl (两侧同一 gathered tensor). 关键：**start=0** on both sides + range **full [0, numExp)** on both sides → 不需 sum split, disjoint 天然不需要. 结果 axiom footprint: `propext + Classical.choice + Quot.sound` (0 shard-specific axioms)。
29.**Assumption axiom 消除到 statement-level hypothesis**（2026-07-04 方案 E）：当 pattern 需要一个"不能从 abstract Store 推出的 well-formed-input assumption"（如 `labels < vocab`），**不要**用 axiom（哪怕收窄到具体 tensor，"axiom 换个包装"信任链一点没变，`#print axioms` 里 axiom 名字还在）。正确做法：把 hypothesis 上升到**stmt 定义**里。改动：
    - 新增 `goal_N_stmt_with_labels : Prop` = `∀ initSM initPM, ... → hlabels_hypothesis → conclusion`，展开 `CoarseLineageHoldsWithInit` 手写 body（因为 auto-generated def 不能改）
    - 改 `pattern_N_target.goal_N` 绑到 new stmt 而非 raw `goal_N_stmt_cut`
    - `prove_goal_N` 接受 hlabels 参数替代 axiom application
    - 删掉 axiom, verify `#print axioms prove_pattern_N` 只有 kernel axioms
    - **Vacuity witness 必写**：`theorem pattern_N_hypothesis_witness : ∃ initPM, hlabels initPM := ...` — 构造具体 store（如 `fun _ => zeroTensor [...]`）证明 hypothesis 可满足。避免陷阱 2 (stmt := False → X = trivially True)。
    - 效果：信任转移到 verifier caller 的 well-formed-input contract（Python 那边加 runtime `assert labels < vocab`）——**不是** verifier 内部的 axiom
    - Vacuity 三陷阱要审：(1) axiom vacuous（老 rma 那种 ∀ vocab), (2) stmt vacuous (hypothesis 从不成立), (3) hypothesis 隐含 False。三者都可用 existence witness 证否。
30.**Lean toolchain 升级 v4.27→v4.31 breakage patterns**（2026-07-04 升级教训）：mathlib v4.27→v4.31 主要打破点：(a) `simpa [lemma] using h` 类型对齐更严 → 用 `rw [lemma]; exact h` 代替; (b) `List.Sublist.cons₂` 改名为 `cons_cons`; (c) `simp made no progress` 在 v4.31 是硬 error 不是 warning → 用 `try simp only [...]`; (d) 部分 `simp only [valAt]` 触发 isDefEq heartbeat 溢出 → 加 `set_option maxHeartbeats 800000 in` 到 theorem 前 (line comment 而非 `/-- -/` docstring 因为 set_option in 不吃 docstring gap). 升级流程：改 `lean-toolchain` + `lakefile.toml` mathlib rev → `lake update` (ulimit -n 65535 避免 file descriptor 耗尽) → `lake exe cache get` (自动下 mathlib olean cache) → `lake build <target>` 逐项目验证。若 lake 报 "some modules have bad imports"，通常是 `_archive/**` 类死代码 import 了不存在的模块。
31.**Comparator honesty audit 全流程**（2026-07-04 首次跑通）：Lean FRO `leanprover/comparator` 是官方可信裁判，验证 3 件事：(a) Solution theorem statement 和 Challenge byte-for-byte 匹配（防 def sneaky 换定义），(b) Solution 只用 permitted_axioms，(c) Lean kernel 接受。setup：
    - toolchain: 项目 + comparator + lean4export 必须匹配同一 Lean version（v4.31+ 内置 leanchecker，之前版本有 native_decide bug）
    - landrun 沙箱可用 `scripts/fake-landrun.sh` 替代（audit 自己的项目时安全够用）
    - Challenge.lean: `theorem X : STMT := by sorry`；Solution.lean: `theorem X : STMT := actual_proof` — 两侧 statement 必须完全一致
    - lakefile.toml 里加 `[[lean_lib]] name = "Challenge"` / `[[lean_lib]] name = "Solution"`
    - config.json: `challenge_module` / `solution_module` / `theorem_names` / `permitted_axioms`
    - **native_decide 会生成 per-caller axioms** `foo._native.native_decide.ax_N_M`，必须一一加入 permitted_axioms（未来考虑用 wildcard 支持）。用 `python3` 解析 `lean4export Solution -- theorem_name` 的 JSON 输出提取名字：resolve hier-name graph, filter `_native.native_decide.ax`。
    - 成功输出: `Your solution is okay!`
    - **额外**：v4.31 内置 `leanchecker` (`lake env leanchecker <module>`) 独立 kernel replay，`--fresh` mode 是最严格审计 — Pattern_1 全通过.
32.**Graph slicing must chase initGoal bridges**（2026-07-06 血教训）：TrainVerify verifier 用 initGoal 做 cross-graph SM-PM agreement bridge（如 `intermediateGoal_11875` 断言 `initSM 7415 = reconstruct(initPM 11875, ...)`）。任何 slicer 想 slice 出 pm/sm subgraph 时**纯 backward-reachability from goal tid 是错的** —— 会 drop 掉那些图边不可达但 initGoal 引用的 write-nodes，导致 half-cut inconsistency（一侧通过计算，另一侧从 unconstrained init leaf 读）。**正确做法**：(A) clone legacy graph verbatim + 只 patch reshape params（最保守），或 (B) slicer 二次遍历时加入所有 `initGoal.tps` 引用的 tid 到 needed set 并保留其 write-nodes。Pattern_3 `build_goal3_faithful.py` V1 踩这个坑，导致 SM 计算走 attention → PM 读 unconstrained leaf 11875 全 layer false。Worker B 定位到根因后重写 slicer 为 clone-legacy 策略。**教训**：verifier init-goal bridge 是 cut structure 的一部分，slicing 时看图边不看 init-goal = 自动裂开。
