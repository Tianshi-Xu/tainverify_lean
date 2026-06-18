# Task: 实现通用 Bridge 渲染器 (per-node, 覆盖一切拓扑) + 回归验证全部 74 个已写 bridge

工作目录: `/home/argustest/.openclaw/workspace/tainverify_lean/trainverify`
所有路径相对此目录(除非写明仓库根 `tainverify_lean/`)。

## 背景与目标
TrainVerify 形式化项目。每个 goal 需要一个 `GoalNBridge.lean` 把已证的 `prove_goal_N_cut`(0 sorry)
包装成无条件的 `goal_N_cut_to_full` + `goal_N_intermediate`,再 wire 进 MainTheorem。

我已搭好 emitter 骨架在 `bridge_emitter/`:
- `parser.py` — 从 Goal_N.lean 解析 IR(sm/pm nodes, shapes, lineage, prereqs)。**已验证可用**。
- `probe.py` — 两阶段构建:emit 临时探针 .lean → 编译 → 反查 full 图 node 索引。**已验证可用**(返回 `{"sm":{tid:{node_idx,op,params}}, "pm":{...}}`)。
- `emit.py` — 端到端入口(family-A 版)。含 `trace_input_sources()`(输入溯源)+ `compute_imports()`。**这两个函数可复用**。
- `renderer.py` — **旧的 family-A 专用渲染器**(只覆盖 multi-tp+0mid+per-rank)。goal_30 回归已通过(编译 exit0, 0 sorry, axioms 干净)。
- `renderer_uni.py` — **我起了个头的通用渲染器**,有 `node_expr`(递归内联)/`pm_full_segment`/算子表。**你要完成它**。
- `SPEC.md` — 设计规格。先读。

**你的任务: 把 renderer_uni.py 做成真正覆盖一切拓扑的通用渲染器,并用全部 74 个已写 bridge 做回归(生成结果编译过 + 0 sorry + axioms 无 sorryAx)。**

## 核心设计(已用 74 个 bridge 验证, 必须遵守)
1. **每个 bridge 恰好 1 个 SM 节点**。复杂度全在 PM 侧。
2. **PM mini-graph = 线性节点列表**。每个节点要么:
   - **mid 节点**(outs 是中间张量)→ 生成一条 `pm_full_<out>` 定理
   - **final 节点**(outs ∈ lineage.tps)→ 并入 `pm_frame_<out>_self`
3. **单节点段落只由 `(op, ins, outs, rank, node_idx)` 决定**。leaf 输入 vs mid 输入在单段里**无区别**,都用 `pm_prefix_eq`。
4. **算子两类**:
   - pointwise(FW_*): ins 字面 `[1661, 603, 604]`, 用 `applyNode_fw_<op>_out`, denote 函数 `fw_<op>`
   - collective(AllToAll/AllGather/AllReduce/Chunk): ins 用 `((List.range K).map (fun r => BASE + r))` 形式, 各有特定 denote 函数和 lemma(见 renderer_uni.py 的 COLLECTIVE_OPS 表)
5. **唯一全局连接**: 终态 `pm_frame_<final>_self` 末尾按**逆拓扑序** `rw [pm_full_X, pm_full_Y, ...]` 逐层展开嵌套表达式(最近层先, 最远层后)。

## 8 段骨架结构(每个 bridge 文件)
照 `denote/gpt_ly4_regen/Goal30Bridge.lean`(multi-tp 0-mid 样本) 和 `Goal44Bridge.lean`(single-tp 12-mid 最复杂样本) 两个金标准:
1. `denote_sm_goal_N_<smOut>` — mini sm 图算 SM 输出 = op(输入)
2. `denote_pm_goal_N_<finalTid>` (single=1个 / multi=4个) — mini pm 图算最终 tp, RHS 是**完全嵌套**表达式(mid 内联)
3. `sm_frame_<smOut>_self` — full sm = mini sm (sm_val + show node + applyNode + sm_prefix_eq)
4. `pm_full_<midTid>` (每个 mid 一个) — full pm 算 mid = op(immediate ins, **不内联**)
5. `pm_frame_<finalTid>_self` (single=1 / multi=4) — full pm 算 final, 末尾逆拓扑 rw 所有 pm_full
6. `goal_N_hInitCut_helper` — 把 prereq intermediate 装成 InitGoalsHold(避免 heartbeat 超时)
7. `goal_N_cut_to_full` — 总装(见下)
8. `goal_N_intermediate` — `cut_to_full prove_goal_N_cut` 包装

## 总装 `goal_N_cut_to_full` 模式(最易错, 照 Goal30/Goal44 抄)
```
intro initSM initPM hSM hPM hInit
set Ssm := denoteGraph sm initSM with hSsm
set Spm := denoteGraph pm initPM with hSpm
have hg<M> := goal_<M>_intermediate initSM initPM hSM hPM hInit   -- 每个 prereq 一行
have hinitC := initGoals_preserved initSM initPM hInit
have hnr : pm_goal_N.numRanks = pm.numRanks := by native_decide
-- shape proofs: 每个 SM/PM 输入 tid 的 shape, 来源分三类:
--   来自 prereq.ts  -> hg<M>.1 + simp [goal_<M>]
--   来自 prereq.tps -> hg<M>.2.1 + simp [goal_<M>, List.map, List.cons.injEq, and_true] + obtain ⟨4个⟩
--   来自 initGoal_W -> hinitC initGoal_W (by simp [initGoals]; decide), 再 .1/.2.1 拆 sm/pm shape
-- hSM<N>/hPM<N>: StoreShapesHold, rcases over InitShapes list, 每条 exact 对应 shape 变量
have hInitCut := goal_N_hInitCut_helper Ssm Spm hinitC hg<M>...
have hcut := h Ssm Spm hSM<N> hPM<N> hInitCut
have hsmf : Ssm <smOut> = denoteGraph sm_goal_N Ssm <smOut> := by rw [hSsm]; exact sm_frame_<smOut>_self initSM
have hpm<T> : Spm <T> = denoteGraph pm_goal_N Spm <T> := by
    rw [denote_pm_goal_N_<T>]; rw [hSpm]; exact pm_frame_<T>_self initPM   -- 每个 final tp 一行
rw [hnr] at hcut
simp only [goal_N, List.map] at hcut ⊢
rw [hsmf, hpm<T>...]
exact hcut
```
`trace_input_sources()` 和 shape proof 生成 family-A 版已在 renderer.py 里写好, **直接搬过来扩展**(对 single-tp 也适用, 只是 final tp 数=1)。

## single-tp vs multi-tp 差异(关键!)
- **multi-tp**(4 final): 4 个 `denote_pm`/`pm_frame`, 终态节点是 4 个独立 per-rank op(各产一个 tp), **无终态 collective**(或 collective 在 mid 层)。lineage.tps 有 4 个。
- **single-tp**(1 final): 1 个 `denote_pm`/`pm_frame`, 终态是一个 collective(AllReduce/AllGather)把 4 个 mid 聚成 1 输出。lineage.tps 有 1 个, ts==tid。
  - `denote_pm_goal_N_<final>` 的 RHS = `allReducePrim K 0 [完全嵌套的 4 个 rank 表达式]`(见 Goal44Bridge 39-54 行)。证法: `simp [pm_goal_N, denoteGraph, List.foldl]; rw [applyNode_X_out]; simp [List.map]; congr 1`
  - `pm_frame_<final>_self`: 见 Goal44Bridge 250-288 行。末尾 `rw [pm_full_<最后层>...]; rw [pm_full_<前面层>...]; rw [show pm.numRanks = 4 from by native_decide]`

## per-rank op 的 denote_pm 细节(multi-tp)
看 Goal30Bridge 44-72 行: 第一个 tp 的 `denote_pm` 只 `repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]; rw [helper]`; 后续 tp 多一行 `congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]`。这个 `repeat rw [applyNode_eq_of_not_mem_outs]` 是跳过 mini 图里前面 rank 的节点。**single-tp 的 denote_pm 不用这个**(用 congr 1 展开嵌套)。

## 算子→lemma 映射的脏点(重要)
有些算子的 applyNode lemma 带 goal 后缀(手证时建的局部引理), 通用表里用无后缀版本可能不存在:
- `FW_contiguous` → 可能只有 `applyNode_fw_contiguous_out_g46`(带后缀)
- `FW_softmax` → `applyNode_fw_softmax_out_g43`
- `FW_div` → `applyNode_fw_div_out_g17` / `_g42`
- multiref 第二/三输出 → `applyNode_fw_multiref2_second_out_gNNN`
**做法**: 渲染前先 `grep -rn "applyNode_fw_<op>_out" denote/gpt_ly4_regen/*.lean` 确认无后缀版本是否存在。
- 若存在无后缀通用版 → 用它。
- 若只有带后缀版 → 该 goal 暂时**跳过**(记进 SKIPPED 清单), 不要硬编后缀(后缀是 per-goal 的不通用)。
- multiref 取第几个输出: 看 mini-graph 节点 outs 长度 + lineage.ts 等于第几个 out。先聚焦单输出算子, multiref 多输出作为已知难点单列。

## multiref 特殊处理
multiref 节点 outs 是 `[a, b]`(双)或 `[a,b,c]`(三)。bridge 取其中一个(lineage.ts/tps 对应的)。
denote 展开用 `applyNode_fw_multiref2_first_out` / `_second_out` / `applyNode_fw_multiref3_*`。
先看 Goal285Bridge(multiref 取第一输出, 无 collective)和 Goal283Bridge(取第二输出 + AllToAll) 的实际写法。
若 multiref 太复杂, 先让非 multiref 的所有拓扑通过, multiref 单列 TODO。

## 实现步骤
1. 读 `SPEC.md`, `renderer.py`(搬 shape proof + hInitCut + cut_to_full 逻辑), `renderer_uni.py`(我起的头), Goal30Bridge.lean, Goal44Bridge.lean(两个金标准)。
2. 完成 `renderer_uni.py`: 实现 `render_universal(n, ir, topo, probe_map, input_sources, prereqs, imports)`, 逐节点生成 8 段。
3. 写新入口 `emit2.py`(照 emit.py, 但调 render_universal, **去掉 family-A 限制**, 任何拓扑都尝试)。
4. **回归测试**: 写 `bridge_emitter/regress.py`, 对每个已写 bridge 的 goal N:
   - 备份原 `GoalNBridge.lean` 到 `/tmp/bridge_backup/`
   - 跑 `emit2.py N --no-compile` 生成
   - `lake env lean denote/gpt_ly4_regen/GoalNBridge.lean`(cwd=trainverify) 编译
   - 检查 exit0 + grep -c sorry == 0
   - **无论成败, 最后从备份恢复原文件**(不能污染已 commit 的 bridge!)
   - 记录 PASS/FAIL/SKIP + 失败原因
5. 跑全部 74 个, 产出覆盖率报告 `bridge_emitter/REGRESSION.md`: 多少 PASS / FAIL / SKIP, 每个 FAIL 的拓扑类型 + 错误摘要。
6. 对 FAIL 的, 按拓扑类型归类修渲染器, 迭代到尽可能高覆盖率。

## 编译命令(关键)
- **必须 `cd /home/argustest/.openclaw/workspace/tainverify_lean/trainverify`** 再 `lake env lean denote/gpt_ly4_regen/GoalNBridge.lean`(import 路径 `denote.gpt_ly4_regen.*` 相对 trainverify/)
- 从仓库根跑会报 "unknown module prefix 'denote'"。
- 单文件编译约 1-5 分钟(native_decide 探针慢)。timeout 给足 600-900s。

## 验收标准
1. `renderer_uni.py` + `emit2.py` + `regress.py` 完成
2. `REGRESSION.md` 报告: 目标 **≥80% 的已写 bridge 回归 PASS**(编译 exit0 + 0 sorry)。multiref / 带后缀 lemma 的可 SKIP 并记录。
3. **绝对不要污染已 commit 的 GoalNBridge.lean**(回归必须备份+恢复)。
4. **不碰** Denote.lean / GeneratedData.lean / 已有的 Goal_N.lean(只读)。
5. 不 commit, 不 push。把所有新文件留在 `bridge_emitter/`。

## 纪律
- lemma 名不确定 → `grep -rn` 确认真名, 不编造。
- 回归污染风险最高: **每次生成前备份, 测完恢复**, 用 git status 自查没有已追踪文件被改。
- 卡在某拓扑 → 记进 REGRESSION.md 的 FAIL/SKIP, 继续下一个, 不要无限循环单个。
- 优先让简单拓扑(0-mid, 单 collective)全过, 复杂的(12-mid 多 collective, multiref)尽力。
- 进度随时写 REGRESSION.md, 别全憋到最后。
