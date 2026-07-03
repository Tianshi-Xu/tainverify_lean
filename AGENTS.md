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