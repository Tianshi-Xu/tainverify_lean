# Bridge Emitter 设计规格 (TrainVerify cut→full 自动化)

> 目标: 给定一个 goal 的结构化数据 (mini-graph + InitShapes + LineageGoal + prereqs),
> 全自动生成 `GoalNBridge.lean` (cut→full frame), 0 sorry, 编译通过。
> 把 GPT 这套剩余 ~160 goal 全自动化, 并为 qwen3/DeepSeek V3 等新架构提供可复用 pipeline。

## 0. 核心论断 (已用 64 个手写 bridge 验证)

bridge 的**每一个 token 都是结构化输入的确定性投影**, 无创造性。
唯一真输入 = 4 个对象, 全部已存在于 `Goal_N.lean` / `GeneratedData.lean`:

1. `sm_goal_N : GraphDecl` — 单机 mini-graph (1 个 SM 算子节点)
2. `pm_goal_N : GraphDecl` — 并行 mini-graph (collective + per-rank ops)
3. `sm_goal_NInitShapes` / `pm_goal_NInitShapes` — 输入张量 shape 表
4. `goal_N : LineageGoal` (ts/tsShape/tps/tpShapes/gatherDim) + `goal_N_prereqs`

bridge 结构由两个正交维度决定 (实测分布见 §5):
- **输出 tp 数**: single-tp (1, 终态 collective 聚成 1 输出) | multi-tp (4, per-rank 输出)
- **中间张量层数**: pm_full 数 ∈ {0,4,8,12} = pm mini-graph 里"非最终 tp"节点的层数 ×4

## 1. 输出文件结构 (固定 8 段骨架)

每个 bridge 文件 = 以下段落的渲染 (段落有无/数量由拓扑决定):

| 段 | 定理名模式 | 数量来源 | 作用 |
|----|-----------|---------|------|
| A | `denote_sm_goal_N_<smOut>` | 1 | mini SM 图算最终输出 = 算子(输入) |
| B | `sm_frame_<smOut>_self` | 1 | full sm 图 = mini sm 图 (经 sm_val + node 字面 + applyNode + sm_prefix_eq) |
| C | `pm_full_<midTid>` | 每个中间张量 1 个 (0/4/8/12) | full pm 图算中间张量 = 算子(上游) |
| D | `denote_pm_goal_N_<tpOut>` | single=1 / multi=4 | mini pm 图算最终 tp |
| E | `pm_frame_<tpOut>_self` | single=1 / multi=4 | full pm = mini pm (引用 pm_full_*) |
| F | `goal_N_hInitCut_helper` | 1 | 把 prereq 的 intermediate 装成 InitGoalsHold (避免单 heartbeat 超时) |
| G | `goal_N_cut_to_full` | 1 | 总装: have hgM + shapes + hSM/hPM + hcut + frame rw |
| H | `goal_N_intermediate` | 1 | `cut_to_full prove_goal_N_cut` 包装成 InitGoalHolds |

## 2. 输入解析 (parser)

从 `Goal_N.lean` 提取 (正则/lean AST 二选一, 先用正则 PoC):
```
sm_nodes   = [(rank, op, ins, outs, params?)]   # 从 def sm_goal_N
pm_nodes   = [(rank, op, ins, outs, params?)]   # 从 def pm_goal_N
sm_shapes  = [(tid, shape)]                       # sm_goal_NInitShapes
pm_shapes  = [(tid, shape)]                       # pm_goal_NInitShapes
lineage    = {ts, tsShape, tps:[(rank,tid)], tpShapes, gatherDim?}  # GeneratedData
prereqs    = [int]                                # goal_N_prereqs
```

## 3. 拓扑分析 (topology)

从 pm_nodes 推导:
- **final_tps** = lineage.tps 的 tid 集合 (mini pm 图里 outs∈这些的节点 = 最终输出节点)
- **mid_tids** = pm mini 图所有 outs - final_tps - pm 输入 = 中间张量 (决定 pm_full 段数量)
- **层次分组**: 按数据流给 mid_tids + final_tps 排拓扑序; 每层一组算子 (collective / per-rank op)
- **single vs multi tp**: len(final_tps)==1 → single; ==4 → multi
- **算子类型链**: 每个节点的 op → 决定用哪个 applyNode helper + 哪个语义引理

## 4. node 索引探针 (probe) — 关键!两阶段构建

bridge 引用 `pm.nodes[IDX]'(by native_decide) = {...}`, IDX 是 full 图 flatten 后位置, **生成期算不出**。
解决: emitter 先 emit 一个临时探针文件, 编译 + `#eval` 反查, 再 emit 正式 bridge。

探针模板 (对每个要在 full 图定位的 tid):
```lean
#eval (List.range pm.nodes.length).filterMap (fun i =>
  if h : i < pm.nodes.length then
    let o := (pm.nodes[i]'h).outs
    (if o = [TID] then some (i, (pm.nodes[i]'h).op, (pm.nodes[i]'h).params) else none)
  else none)
```
SM 同理用 sm.nodes。输出解析成 `{tid: (node_idx, op, params)}` 映射表, 喂给渲染器。
⚠ AllToAll/AllGather/multiref 这类 ins 用 `(List.range 4).map (fun r => BASE + r)` 形式, 探针要确认 BASE。
⚠ node 不一定相邻 (旁支 goal 穿插, 如 goal_283 AllToAll 用 351/353/355/357), 必须逐 tid 探, 不能假设连续。

## 5. 算子 → 引理映射表 (op_lemma_map) — 已知脏点

| op (mini-graph) | applyNode helper | 语义分配引理 (cut 已证, bridge 不重证) |
|-----------------|------------------|----------------|
| FW_gelu | applyNode_fw_gelu_out | fw_gelu_allGatherPrimDimN_eq |
| FW_linear | applyNode_fw_linear_out | (column/row split 各异) |
| FW_add | applyNode_fw_add2_out | (binary, elemwiseAdd) |
| FW_matmul | applyNode_fw_matmul_out | — |
| FW_view | applyNode_fw_view_out | — |
| FW_layernorm | applyNode_fw_layernorm_out | — |
| FW_softmax | applyNode_fw_softmax_out_g43 ⚠ | — |
| FW_div | applyNode_fw_div_out_g17 / _g42 ⚠ | — |
| FW_contiguous | applyNode_fw_contiguous_out_g46 ⚠ | — |
| FW_multiref (2-out, 取1) | applyNode_fw_multiref2_first_out | — |
| FW_multiref (2-out, 取2) | applyNode_fw_multiref2_second_out_gNNN ⚠ | — |
| FW_multiref (3-out) | applyNode_fw_multiref3_{first,second,third}_out_gNNN ⚠ | — |
| AllToAllPrim | applyNode_allToAllPrimWithDims_out | — |
| AllGatherPrim | applyNode_allGatherPrimDimN_out_thm | — |
| AllReducePrim | applyNode_allReducePrim_out | — |
| ChunkPrim | (per goal) | — |

**脏点**: 带 `_gNNN` 后缀的是手证时建的**局部引理**, 不通用。
emitter 必须:
1. 维护一张干净映射表 (无后缀版本是目标)。
2. **缺引理时报警** + 生成一个"待补 applyNode 引理"的 stub 清单, 让人/后续 worker 补全到共享库。
3. 长期: 把所有 `_gNNN` 局部引理**提升 (lift)** 成通用引理 (无后缀), 收进 `OperatorLemmas.lean`。这是 qwen3 复用的前提。

## 6. 通用引理 (跨 goal, 无后缀, 直接引用)
`mem_of_shapeEnvOfList_eq_some`, `initGoals_preserved`, `reconstructWithDim_singleton`,
`reconstructWithDim_cons_cons_nonscalar`, `sm_val`, `pm_val`, `sm_prefix_eq`, `pm_prefix_eq`,
`applyNode_eq_of_not_mem_outs`.

## 7. 渲染器 (renderer)
Jinja2-style 模板 (每段一个), 参数 = parser+topology+probe+op_map 的合并字典。
固定 set_option 头 + namespace + import。
import = prereq 依赖图传递闭包里的"直接上游 bridge" (主链最高 N + 旁支 goal)。
→ 用 prereq 列表算: 主链 = max sequential prereq 的 bridge; 旁支 = prereq 里不在主链覆盖范围的 (residual 257+)。

## 8. wire 进 MainTheorem
- 在 import 区加 `import denote.gpt_ly4_regen.GoalNBridge`
- 删 `goal_N_cut_to_full ... := by sorry` (或注释式 stub)
- 幂等: 已 wire 则跳过。

## 9. 验证 (verify) — 每个生成必跑
1. `lake env lean GoalNBridge.lean` EXIT 0, grep -c sorry == 0
2. `#print axioms goal_N_intermediate` 无 sorryAx (白名单: propext/Classical.choice/Quot.sound/ofReduceBool/trustCompiler/applyNode系列)
3. `git diff bc19002 -- Denote.lean GeneratedData.lean` 为空 (没碰核心)
4. MainTheorem 整体编译过

## 10. 架构无关性 (qwen3 / DeepSeek V3 复用边界)
- **§5 干净引理库 + §6 通用引理** = 架构无关。算子相同直接复用。
- **emitter 代码本身 (§1-§9)** = 架构无关。换模型 = 换 Goal_N.lean 输入, 重跑。
- 新架构要补: (a) 新算子的 applyNode + 分配引理 (RMSNorm/RoPE/SwiGLU/MoE/MLA); (b) cut 模板 (新 sharding 模式); (c) 图提取器适配。
- bridge 层 100% 自动, 不需为新架构改 emitter。

## 实现顺序
1. parser + topology (纯 Python, 无 Lean 依赖) — 可单测
2. probe 子系统 (emit 临时 .lean + lake env lean + 解析 #eval 输出)
3. op_lemma_map + 缺失报警
4. renderer (8 段模板, 先覆盖最常见的 single-tp/multi-tp × {0,4,8} 中间层)
5. verify + wire
6. 用已写的 goal_46/52/53 做回归: 生成结果应与手写**语义等价** (编译过 + 0 sorry + axioms 干净), 不要求逐字节相同
