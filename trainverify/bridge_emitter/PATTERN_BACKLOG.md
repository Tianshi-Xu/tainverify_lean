# Emitter Pattern Backlog — 泛化未覆盖 pattern

目标: 从"复刻已证 pattern"升级到"用 emitter 直接证未证 goal"(拿到新命题，跳过 LLM，脚本直接生成桥)。

## 当前状态 (2026-06-17)
- written_goals 回归: **56 PASS / 0 FAIL / 24 SKIP** (A 8 + B 7 + C 3 + D 6 = **24 全部可 emitter 生成**, 待并入回归基线)
- **零 SKIP 未覆盖**。零真失败。
- **Family A + B + C + D 全部完成** 🎉

## 关键发现 (de-risking spike 已验证 ✅)
- multiref-2-output 的 `applyNode_fw_multiref2_second_out_gNNN` lemma 是 **per-goal 后缀版**，定义在 **Denote.lean (不可改文件!)**。
- 但 lemma body **完全 goal-agnostic**(只依赖 applyNode/evalOp_fw_multiref/storeSet，都在 Denote.lean)。
- **策略: emitter 在每个生成桥顶部发一个 `private` 本地通用版** `applyNode_fw_multiref2_second_out_local`，不依赖 Denote.lean 的后缀版。
- **g259 spike (改手写版用本地 lemma + 去掉 Goal257Bridge import) → 编译 RC=0, 56s, 0 sorryAx。验证通过。**

## Backlog (按 payoff 排序)

### Family A: multiref-2-out 无 collective (8 goals) ✅ 全部完成 (2026-06-17)
- goals: 259, 261, 263, 269, 273, 277, 285, 293 — **全部 emitter 生成 + 编译 RC=0 + 0 sorryAx**
- 结构: SM=FW_multiref 取某输出位; PM=4×FW_multiref 同输出位 = 输入直通
- 需要: 本地 `multiref2_second_out_local` lemma + denote_pm/sm 第二输出 codegen + multi-final 总装
- 模板: 手写 Goal259Bridge (已完整研读)
- 注意: g261/263 可能是 **first_out** 变体(看 `applyNode_fw_multiref_first_out_g261` 存在)，要分别确认取第几输出

**子族 A2 (multiref-2-out 第二输出, 无 collective) — ✅ 已实现 (2026-06-16)**
- goals: 259, 269, 273 — **全部 emitter 生成 + 编译 RC=0**
  - g259: 62s, g269: 61s, g273: 62s, 全 0 sorryAx (对标手写 56s)
- 实现: renderer_uni.py 加 `is_multiref2_second()` + `render_multiref2_second()` + `_multiref2_second_skips()` + `MULTIREF2_SECOND_LOCAL` 本地 lemma；emit2.py probe 改 `multi_out` 成员匹配(`t ∈ o` 而非 `o=[t]`) + 家族感知 tid 选择(用 lineage.ts/final_tps 而非 outs[0])；renderer.py `cut_to_full_block` 加 `frame_via_denote` 参数
- **关键坑 (踩过)**:
  1. probe 对多输出节点 `o=[t]` 精确匹配失败 → 改成员 `t ∈ o`
  2. SM final 是 outs[1] 不是 outs[0]，probe/render 都要用 lineage.ts
  3. denote_pm skip 顺序: foldl 从**最外层(node K-1)往内剥**，所以 outer skips(on final tid)=K-1-tgt_idx, 然后 lemma, 然后 inner skips(on xTid)=tgt_idx。一开始写反了导致 rewrite failed
  4. 总装 hpm 不能用 `rw [denote_pm_goal_N_tp]` 前缀(默认家族需要, 本家族 pm_frame 已是正确形式) → `frame_via_denote=False`。带错前缀会 hang 3min+
- **子族 A1 (取第一输出 + 多 tps, g285) — ✅ 已实现 (2026-06-17, 彩叶)**: g285 是 2-out 取**第一**输出(idx=0, params=[2]) + multi-tps gatherDim=1, 输入源 goal_54 (ts=637 [1,8,32], tps=2201-2204 [1,2,32])。
  - **关键洞见**: A1 根本不需要新 renderer 路径——`is_multirefN_nth` 的 N=2/idx=0 特例已完全覆盖。之前标记“结构不同, 单独做”是误判: idx=0 lemma 无距离参 (`applyNode_fw_multiref2_out0_loc` 零 hyp), multi-tps shape 提取走和 g261 一样的 ts/tp_by_w 通道 (goal_54 与 goal_5 同形)。
  - emit2.py 零改动直接生成 (5 imports, orig_imports 自动复用 Goal54Bridge+Goal283Bridge) → 编译 RC=0 **61s**, #print axioms 干净 (标准白名单, 无 sorryAx)。验证: git status 仅已知 M+BridgeKit ??; Denote/GeneratedData 0-diff。

**子族 A3 (3-output multiref, params=[3], 取任意输出位) — ✅ g261/g263 已实现 (2026-06-16)**
- goals: 261(取第1输出 idx=0), 263(取第2输出 idx=1) — **都 emitter 生成 + 编译 RC=0**
  - g261: 64s, g263: 64s, 均 0 sorryAx (对标手写版)
- **关键洞见**: N-输出 multiref 的**任意**输出 = 输入。因为 storeSet/find? 返回第一个匹配 pair 的值，而 multiref 所有输出 pair 的值都是 `s x`——所以只要目标 tid 与**严格在它之前**的输出不同就能得 `s x`。A2 是 N=2,i=1 的特例。
- 实现: renderer_uni.py 加 `is_multirefN_nth()` + `render_multirefN_nth()` + `_multirefN_nth_local()`(生成 N 个 private 本地 lemma，每个 out位一个，idx 位需 idx 个“较早输出≠目标”假设) + `_multirefN_nth_pm_skips()` + `_multirefN_nth_apply()`；emit2.py probe 条件加 A3 (用 multi_out 成员匹配 + lineage.ts/final_tps 选 tid)。**跳过项用通用库 lemma `applyNode_eq_of_not_mem_outs`**(整节点输出集，任意输出数，比位置特定的 passthrough 更鲁棒)。
- **关键坑 (踩过)**:
  1. pm_frame 末尾忘了 `rw [pm_prefix_eq ...]` → 报 unsolved goals(`denoteGraph (take N pm.nodes) initPM x = denoteGraph pm initPM x`)。i=0 和 i=1 **都需** prefix_eq。
  2. idx=0 的 apply 项不需 `by decide` 距离参；idx=i 需 i 个 `(by decide)`(较早输出≠目标)。
  3. 生成主身 + native_decide 全图 → 单 goal 编译 ~64s，正常。
  4. 装配用 `cut_to_full_block(..., frame_via_denote=False)`(同 A2，pm_frame 已是直接形式)。
- **A3 剩余 g277 — ✅ 已实现 (2026-06-16, 彩叶)**: 第2输出(idx=1, outs=[961,965,969]选965), 依赖链 prereqs=[2..30,257..271]。renderer 零改动直接生成 (emit2.py 自动复用手写桥的 orig_imports, 13 imports 全有 olean) → 编译 RC=0 **64s**, #print axioms 干净 (无 sorryAx, 标准白名单 + applyNode_allGatherPrimDimN_out/fw_linear_out 等域公理)。**结论: 之前标记的“import 依赖链卡点”不成立——deps 已全部 built, emit2.py orig_imports 路径自动处理。** 验证: git status 仅已知 M + BridgeKit ??; Denote/GeneratedData 0-diff。
- **A3 剩余 g293 — ✅ 已实现 (2026-06-17, 彩叶)**: 第3输出(idx=2, params=[3], outs=[3607/3609/2313..]选 2313-2316), multi-tps gatherDim=1, prereqs 含 285。
  - renderer N=3/idx=2 路径(`applyNode_fw_multiref3_out2_loc`, 带 h02/h12 两个距离参)零改动直接生成 → 编译 RC=0 **64s**, axioms 干净。
  - **import 链非阻塞**: g293 import Goal285Bridge, 而**手写版 Goal285Bridge.olean 早已在 .lake/build 里** (2026-06-16 14:16), 所以即便我只往 /tmp 写 g285, g293 的依赖 olean 也满足。之前“必须先做 A1”的顺序约束在 olean 层面本就不成立——但逻辑上 A1 仍是 A3 完成的前置(共享 multiref-first-out 语义)。

### Family B: multiref-2-out + AllToAll (7 goals) ✅ 全部完成 (2026-06-17, 彩叶)
- goals: 257, 267, 271, 275, 279, 281, 283 — **全部 emitter 生成 + 编译 RC=0 + 0 sorryAx**
  - g257: 60s, g267: 60s, g271: 59s, g275: 61s, g279: 61s, g281: 59s, g283: 60s (对标手写 56-64s)
- 结构: SM=FW_multiref 取某输出位; PM=4×FW_multiref 同输出位 MID → 4×AllToAllPrim finals。
- **关键洞见**: Family B = Family A 的 multiref-任意输出位 + 顶上套一层 collective。mid = 输入直通 (任意 N-out 任意 i 位都成立), collective 消费这些 mid 的输入 tid。lineage cut(collective == chunk/gather of gathered SM input)在 INVIOLABLE 的 `prove_goal_N_cut` 里, emitter 只负责 full<->mini 框架。
- 实现: renderer_uni.py 加 `_mref_mid_index()` + `is_multiref_first_collective()`(名字保留向后兼容，实际覆盖任意输出位) + `render_multiref_first_collective()`; emit2.py probe tid 选择加 Family B 分支(用 outs[idx] 选 mid, multi_out 成员匹配)。idx==0&2-out 用通用 `applyNode_fw_multiref2_first_out`(Denote.lean 现成, 零 hyp); 其余 (N,i) 复用 A3 的 `_multirefN_nth_local` 本地 lemma。
- 变体分布: (2,0)=257/267/271/281 走通用 first-out; (3,0)=275; (3,2)=279; (2,1)=283 走本地 lemma。
- **关键坑 (踩过)**:
  1. collective 节点的 `pm_frame_self` 不能用通用 `_node_literal`——它对 list-kind collective 生成 range 形式 `(List.range K).map (fun r => base+r)`, 假设 ins 连续。但 Family B 的 collective ins = multiref mids, 常常非连续(如 stride-6 [3413,3419,3425,3431])。拿 `_node_literal` 会导致 `show pm.nodes[i] = {...} by native_decide` 判 false。→ 改用**显式 ins 列表**。
  2. denote_pm collective 身体用 `repeat applyNode_eq_of_not_mem_outs` + `applyNode_<coll>_out` + `congr 1`——`congr 1` 能收是因为 mini-graph 里 multiref mid 的 store 值 defeq 于输入 tid 的值(storeSet/find? 在具体节点上可 unfold)。
  3. 装配用 `cut_to_full_block(frame_via_denote=False)`(同 A2/A3, pm_frame_self 已是 mini 形式)。
- **import 链非阻塞**: emit2.py orig_imports 自动复用手写桥的 imports, 所有 prereq olean 已 built。
- 验证: git status 仅已知 M + BridgeKit ??; Denote/GeneratedData 0-diff; #print axioms 干净(标准白名单, 无 sorryAx)。universal 路径 g9 回归 RC=0 无影响。

### Family C: multiref-i-th-out + AllGather (3 goals) ✅ 全部完成 (2026-06-17, 彩叶) — **零 emitter 改动**
- goals: 265, 289, 291 — **全部 emitter 生成 + 编译 RC=0 + 0 sorryAx**
  - g265: 58s, g289: 58s, g291: 59s (对标手写 ~56s, axioms 干净)
- 结构: SM=FW_multiref 取某输出位; PM=4×4-output multiref MID → 单个 AllGatherPrim final (不同于 B 的 4 finals!)。变体: (3,2)=265, (3,0)=289, (3,1)=291, 全是 3-out。
- **关键洞见**: 起初以为 Family C 需要同 B 的出口位推广 + AllGather 的不同 full lemma 名。实际上 B 的 `is_multiref_first_collective` + `render_multiref_first_collective` **零改动直接覆盖**——因为:
  1. detector 不拘于 collective op kind (只要 `is_collective(nd.op)` 且输入是 mid)
  2. COLLECTIVE 表里 AllGatherPrim 早就有 mini=`applyNode_allGatherPrimDimN_out`/full=`applyNode_allGatherPrimDimN_out_thm`/form=`p0 K rank LIST`
  3. `_collective_expr` 已处理该 form
  4. final 个数 K=1 不是问题 (loop 天然适配)
- 纯**验证式运行**: emit2.py + renderer_uni.py **零行改动**, 直接生成+编译+验证 axioms 全过。
- axioms 比 B 还净一点: 仅标准白名单 + erfFn/expFn/piScalar/sqrtFn (无 `Lean.ofReduceBool`/`scalarToNat`, 因为 AllGather 不走 ofReduceBool 路径)。
- 验证: git status 仅已知 M + BridgeKit ??; Denote/GeneratedData 0-diff; bridge_emitter 零表面变动。

### Family D: pointwise op 缺 lemma (6 goals)
拆为两个子族:
- **D1 (pointwise-final)**: g17(FW_div+ChunkPrim), g42(FW_div+AllToAll), g43(FW_softmax 纯) — 最终节点是 pointwise op。
- **D2 (collective-final)**: g18(FW_softmax+AllToAll+AllGather), g21(FW_contiguous+AllToAll+AllGather), g46(同 g21) — 最终节点是 AllGather, pointwise 在 mid。

**子族 D1 (pointwise-final) — ✅ 全部完成 (2026-06-17, 彩叶)**
- goals: 17, 42, 43 — **全部 emitter 生成 + 编译 RC=0 + 0 sorryAx**
  - g43(FW_softmax 纯, 4×softmax leaf-input): 61s
  - g17(FW_div+ChunkPrim, 4×chunk mid → 4×div final): 57s
  - g42(FW_div+AllToAll, 4×allToAll mid → 4×div final): 61s
  - axioms 均为标准白名单 + applyNode_allGatherPrimDimN_out/fw_linear_out/erfFn/expFn/piScalar/scalarToNat/sqrtFn
- **关键洞见**: FW_div/FW_softmax/FW_contiguous 的 `applyNode_fw_*_out_gNNN` lemma 在 INVIOLABLE Denote.lean 里，但身体**完全 goal-agnostic**(普遍量化 g/s/rank/tids/params, evalOp 由 rfl)。同 multiref 家族策略——emitter 顶部发一个 `private ..._loc` 本地通用版，零依赖 Denote.lean 后缀版。这 3 个 op 本质上跟 `fw_gelu`/`fw_layernorm` 一样走现有 universal renderer pointwise 路径，只是以前被 `SKIP_OPS` 拦住。
- 实现 (renderer_uni.py):
  1. `POINTWISE` 表加 3 个 op (helper 指向 `_loc` 本地名); 从 `SKIP_OPS` 移出(只留 FW_multiref)。
  2. `OP_LOCAL_LEMMA` 存 3 个 op 的本地 lemma 文本; `_emit_local_lemmas(ir)` 按 sm+pm 实际出现的 D-op 去重发射 (非-D goal 零发射, 不污染)。
  3. `OP_LOCAL[op].post` 存后置规范化 tactic: **fw_div 需 `norm_num`**(把 `((params.head?.getD 1 : Nat) : Scalar)` 算成字面量); softmax/contiguous post=""。
  4. `_pointwise_expr` 对 fw_div 特处理: RHS = `fw_div ((c : Nat) : Scalar) (arg)`, c=params[0]。
  5. post tactic 插入位置: `denote_sm_block`/`sm_frame_block` 末尾(无 congr); `pm_frame_block` 在 mid_rw + numRanks 重写之后末尾; `denote_pm_block` has_mid 路径靠 `try congr 1` 吸收 param **不需** post(关键: congr 把 scalar 子目标自动 rfl 掉)。
- **关键坑 (踩过的)**:
  1. fw_div scalar param 不需到处 norm_num。denote_pm 的 has_mid 路径用 `congr 1` 后 param 子目标 (`[2].head?.getD 1 = 2`) defeq 自动收，只有 denote_sm/sm_frame/pm_frame(无 congr 处) 才需 norm_num。
  2. g17/g42 的 fw_div 是 **final** 节点(1369-1372 = lineage.tps), chunkPrim/allToAll 是 mid——所以 fw_div 走 `pm_frame_block`, 不是 `pm_full_block`。norm_num 要在 `rw [pm_full_xxx]` + `rw [pm.numRanks=4]` **之后**。
  3. 生成版 pm_frame RHS 用字面 4 (chunkPrimDimN 1 4 0), 手写版用 pm.numRanks——生成版多一句 `rw [show pm.numRanks = 4 ...]`(any_collective=True 本就有), 等价。
- **import 链非阻塞**: emit2.py orig_imports 自动复用手写桥 imports, 所有 prereq olean 已 built。
- 验证: git status 仅已知 M + BridgeKit ??; Denote/GeneratedData 0-diff; 手写 Goal{17,42,43}Bridge 零改动(只写 /tmp)。universal 路径 g9/g30 干净(零本地 lemma 发射)无回归。

**子族 D2 (collective-final) — ✅ 全部完成 (2026-06-17, 彩叶) — 零 emitter 改动**
- goals: 18, 21, 46 — **全部 emitter 生成 + 编译 RC=0 + 0 sorryAx**
  - g18 (FW_softmax+AllToAll+AllGather): 57s
  - g21 (FW_contiguous+AllToAll+AllGather): 57s
  - g46 (FW_contiguous+AllToAll+AllGather): 57s
  - axioms 均为标准白名单 + applyNode_allGatherPrimDimN_out/fw_linear_out/erfFn/expFn/piScalar/scalarToNat/sqrtFn
- **关键洞见**: D1 里为 FW_softmax/contiguous 发的 `_loc` 本地 lemma + POINTWISE 表的加入已经足够覆盖 D2。**零 emitter 代码修改本轮。**
- **之前担心的 “pointwise-mid 夹在两层 collective 中间 universal 路径可能收不了” 是误判**: universal `denote_pm_block` 的 collective 路径 (`simp only [pm_goal_NN, denoteGraph, List.foldl]; rw [applyNode_allGatherPrimDimN_out]; simp only [List.map]; try (set_option maxHeartbeats 800000 in congr 1)`) 实际上能处理任意 pointwise mid 。原理:
  1. `simp only [denoteGraph, List.foldl]` 纯重写展开整个 foldl 链 (节点不多时可行)
  2. `applyNode_allGatherPrimDimN_out` 重写 final
  3. `simp only [List.map]` 规范化 args list
  4. `congr 1` 以列表元素为单位匹配, 每个 pointwise mid 的 `applyNode` 重写以 storeSet/find? 上的 defeq 关闭 (mini-graph 节点量在 8-9 个, 在 800000 heartbeat 阈值内)
- **关键踩过的冱点 (心里担心但身体不为)**: g21 手写版用 `applyNode_fw_contiguous_out_g21` (将 fw_contiguous 当 identity 的特化版), 生成版用 `applyNode_fw_contiguous_out_loc` (wrapper 版). 两者不冲突——`denote_pm_goal_NN_TP` 只是本地辅助 lemma, 表述 RHS 的选择与 cut 证明独立。只要 `denote_pm` 和 `pm_frame` 的 RHS 形式一致 (都是 wrapper 形) 就可以拼接。
- 验证: git status 仅已知 M + BridgeKit ??; Denote/GeneratedData 0-diff; 手写 Goal{18,21,46}Bridge 零改动(只写 /tmp); bridge_emitter 零改动(mtime 未变)。

## 验证标准 (每个 family 完成时)
1. 该 family 所有 goal `emit2.py` 生成成功 + 独立编译 RC=0
2. `#print axioms` 干净(无 sorryAx，标准白名单)
3. 编译时间合理(对标手写)
4. 不碰 Denote.lean / GeneratedData.lean(0-diff 铁律)
5. targeted regression 无回归

## 进度
- [x] Family A (multiref-2-out 无 collective): **全部完成** — A2(259/269/273 第二输出) ✅; A3(261/263/277 任意输出位, 277@64s) ✅; A1(285 第一输出+multi-tps, 61s) ✅; A3剩余 g293(第3输出, 64s) ✅。**关键: A1+g293 零 renderer 改动，`is_multirefN_nth` 任意 N/idx 已覆盖。**
- [x] Family B (+AllToAll): goals 257,267,271,275,279,281,283 — **全部完成 (2026-06-17, 彩叶)**。全部 RC=0 ~59-61s, 0 sorryAx。新增 `is_multiref_first_collective`/`render_multiref_first_collective`(任意 N-out 任意 i 位 multiref MID → collective)。复用 A3 本地 lemma + 通用 first-out。坑: collective pm_frame_self 必须用显式 ins 列表(非连续 mid)。
- [x] Family C (+AllGather): goals 265,289,291 — **全部完成 (2026-06-17, 彩叶)、零 emitter 改动**。RC=0 ~58-59s, 0 sorryAx, axioms 干净。B 的 detector + renderer 状似表驱动直接覆盖 (AllGatherPrim 在 COLLECTIVE 表, `applyNode_allGatherPrimDimN_out_thm` 是 full lemma)。变体全 3-out: (3,2)=265, (3,0)=289, (3,1)=291。K=1 final 不会牊 loop。
- [x] Family D D1 (pointwise-final: FW_div/softmax): g17/g42/g43 — **完成 (2026-06-17, 彩叶)**。RC=0 57-61s, 0 sorryAx。关键: 3 个 D-op 的 `applyNode_fw_*_out_gNNN` 是 goal-agnostic(evalOp 由 rfl), 发 `private ..._loc` 本地版 + 移出 SKIP_OPS 加入 POINTWISE 即可走现有 universal pointwise 路径。fw_div scalar param 靠 has_mid 路径的 `congr 1` 吸收(仅 denote_sm/sm_frame/pm_frame 需 norm_num)。
- [x] Family D D2 (collective-final: FW_softmax/contiguous over AllGather): g18/g21/g46 — **完成 (2026-06-17, 彩叶) — 零 emitter 改动**。RC=0 均 57s, 0 sorryAx, axioms 干净。D1 里为 softmax/contiguous 发的 `_loc` 本地 lemma 已足够覆盖 D2。之前担心的 “pointwise mid 在两层 collective 之间 universal 路径可能收不了” 为误判——`simp only [denoteGraph, List.foldl] + applyNode_allGatherPrimDimN_out + simp only [List.map] + try congr 1` 在 800000 heartbeats 内能完成 8-9 节点 mini-graph 的全路 defeq 关闭。

## 🎉 backlog 清空 (2026-06-17, 彩叶)
所有 24 个原 SKIP'd goals 均可由 emitter 生成, 全部 RC=0 0 sorryAx 。下一步: 并入回归基线 (written_goals.txt), 取代对应的 SKIP 标记。

## 2026-06-17(晚) 验证 + 清理 run (彩叶)
- **无 pending 子族**: backlog 确为已清空。本 run 端到端复验: emitter 现态对全部 5 个家族代表 (g285/g293/g257/g265/g18) `--no-compile` 生成 OK; g259(A2) + g18(D2) 实编译 RC=0 0 sorry。`renderer_uni.py`/`emit2.py` 完好。
- **`regress_results.json` 是 emitter 扩展前的旧快照** (仍记 24 个 SKIP), 不反映现态 — 不要被它误导。真实状态以 emit2.py 直生为准。
- **修复了一次纪律违规 (前一 run 06-17 08:15 批次)**: 该批次把 emitter 生成内容**直接覆写进了 tracked 手写桥** (Goal17/18/257/265/285/293), 违反铁律(1)“只写 /tmp”。已恢复:
  - 17/18/265/285/293 → `git checkout HEAD`(回到干净手写, 0-diff; 验证 backup==HEAD)
  - Goal257 → 用 `/home/argustest/.copilot/session-state/bridge_backup/Goal257Bridge.lean`(BridgeKit-refactor 版, 即既定的 known-M 态; HEAD 版是 refactor 前的, 不能用 checkout)
  - 被覆写内容已存 `/tmp/clobber_audit_20260617/` 留痕。
- **清理后 git status 回到既定基线**: tracked M 仅 {Goal3,4,7,257,263} + MainTheorem(goal_65 wiring, 另一 workstream) + BridgeKit.lean ??; Denote.lean & GeneratedData.lean 0-diff; 24 个目标桥无一以 ?? 漂在外。
- **教训给后续 run**: 生成只许进 /tmp。若发现 tracked 桥被改成 `AUTO-GENERATED by bridge_emitter` 头, 就是被覆写了, 按上面方式恢复 (区分 known-M 的 BridgeKit-refactor 文件用 backup, 其余用 git checkout)。
