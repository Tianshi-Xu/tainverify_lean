# Task: 证两个 TrainVerify bridge — goal_283 + goal_54 — 并 wire 进 MainTheorem

工作目录: `/home/argustest/.openclaw/workspace/tainverify_lean/trainverify`
所有路径相对此目录。模型架构验证项目, bridge 是"cut → full"的 frame 包装。

## 背景: bridge 是什么
每个 `Goal_N.lean` 已有 `prove_goal_N_cut`(0 sorry, 假设 prereq 成立证局部等价)。
bridge(`GoalNBridge.lean`)用拓扑序上已证的 `goal_M_intermediate` 消掉 cut 的假设, 产出无条件 `goal_N_cut_to_full` + `goal_N_intermediate`。
**纯模板填空, 无创造性**。照已有 bridge 抄, 只换 tid/node/op/shape/prereq。

## 顺序: 先 goal_283(goal_54 依赖它), 编译过再 goal_54。

---

## PART 1: goal_283 (模板 = Goal281Bridge.lean 逐字改)

### 结构
- 它是 goal_281 的**第二输出姊妹**, 共享同一 `FW_multiref(628)→[977,981]` 节点。
  - goal_281 取**第一输出 977**; goal_283 取**第二输出 981**。
- SM: node **53** = `FW_multiref(628)→[977,981]`, 取第二输出 981。 [1,8,32]
- PM: FW_multiref nodes **346/347/348/349** → 各 `[3557+8r, 3559+8r]`(取第二输出 3559/3567/3575/3583);
      然后 AllToAll nodes **351/353/355/357**(⚠ 非相邻! 350/352/354/356 是 goal_281 的, 穿插) →2193/2194/2195/2196, params=[2,1] (idim=2 odim=1)。
- goal_283 LineageGoal: `ts:=981, tsShape:=[1,8,32], tps:=[2193,2194,2195,2196], tpShapes:=4×[1,2,32], gatherDim:=1`
- prereqs = goal_2..49 + 257,259,...,279 odd (60 个)。完全等于 goal_281_prereqs(去 GeneratedData/Goal_283.lean 核对精确顺序)。
- 输入: 628 来自 goal_49 (dim2-shard tps 2057-2060 [1,8,8])。

### 做法
1. `cp denote/gpt_ly4_regen/Goal281Bridge.lean denote/gpt_ly4_regen/Goal283Bridge.lean`
2. 打开 Goal281Bridge.lean **完整读一遍**, 理解它如何取第一输出(977)。goal_283 改成取第二输出(981)。
   - multiref 第二输出的 helper: 找 `applyNode_fw_multiref2_second_out` 或类似(grep `multiref2` 在所有 .lean)。如果 281 用的是 `_first_out`, 283 要对应的 `_second_out`。先 `grep -rn "multiref2.*out" denote/` 确认引理名。
3. 全文替换: 281→283, 977→981, 第一输出 tid→第二输出 tid (3557→3559, 3565→3567, 3573→3575, 3581→3583), AllToAll node 350/352/354/356→351/353/355/357, AllToAll out tid(goal_281 的)→2193/2194/2195/2196。
4. prereq 列表 / rcases 分支数 / hgN 块: 按 goal_283_prereqs 精确对齐(数量与 281 相同, 60 个)。
5. SM/PM InitShapes 顺序: 读 `Goal_283.lean` 里 `sm_goal_283InitShapes` / `pm_goal_283InitShapes` 的**确切顺序**, hSM/hPM 的 rcases 分支按该顺序 exact 对应 shape 假设。
6. wire: MainTheorem.lean 找 `goal_283` 的行(可能是 `goal_283_cut_to_full ... := by sorry` 或注释式)。加 `import ...Goal283Bridge`(在文件 import 区), 删对应 sorry stub。
   - ⚠ 看 Goal281Bridge 是怎么 wire 的(commit 208bdd2 风格), goal_283 照做。

### 验证 goal_283
- `cd /home/argustest/.openclaw/workspace/tainverify_lean && lake env lean trainverify/denote/gpt_ly4_regen/Goal283Bridge.lean` → EXIT 0, 0 error
- `grep -c sorry` Goal283Bridge.lean → 0
- 独立 #print axioms 检查无 sorryAx(可加临时 `#print axioms goal_283_intermediate` 跑一次看输出, 只能有 propext/Classical.choice/Quot.sound/ofReduceBool/trustCompiler/applyNode 系列)

---

## PART 2: goal_54 (脚本已写好, 但依赖 goal_283)

`gen_goal54_bridge.py` 在**仓库根** `/home/argustest/.openclaw/workspace/tainverify_lean/gen_goal54_bridge.py` 已就绪。
它 import Goal53Bridge + Goal283Bridge(part1 证完后就存在了)。

### 做法
1. goal_283 编译过后: `cd /home/argustest/.openclaw/workspace/tainverify_lean && python3 gen_goal54_bridge.py`
   → 生成 `trainverify/denote/gpt_ly4_regen/Goal54Bridge.lean`
2. 编译: `lake env lean trainverify/denote/gpt_ly4_regen/Goal54Bridge.lean`
3. 若有 error: 大概率是 (a) InitShapes 顺序 / rcases 分支数不匹配, (b) multiref/add helper 名, (c) node 索引。
   - 读 error, 对照 `Goal_54.lean` 的 mini-graph + InitShapes 修脚本里对应常量, **改脚本不改生成文件**(改完重跑脚本)。
   - goal_54 结构(脚本注释里有): SM node 58 FW_add(981,636)→637; PM AllToAll 380-383(params[2,1]) + FW_add 384-387。inputs 636(goal_53) + 981(goal_283)。
4. wire goal_54: MainTheorem.lean line ~454 `goal_54_cut_to_full ... := by sorry`。加 import Goal54Bridge, 删 sorry。

### 验证 goal_54
- Goal54Bridge.lean 编译 EXIT 0, 0 sorry
- MainTheorem.lean 整体: `lake build` 对应 target 或 `lake env lean trainverify/denote/gpt_ly4_regen/MainTheorem.lean` EXIT 0

---

## 最终验收(两个都做完)
1. 两 bridge 各 0 sorry, 编译 EXIT 0
2. MainTheorem.lean 编译通过, goal_283 + goal_54 都 wire(对应 sorry 已删)
3. `git diff bc19002 -- trainverify/denote/gpt_ly4_regen/Denote.lean` 为空(没动核心语义文件)
4. git add 两个新 Bridge + MainTheorem + (gen_goal54 如有改动), commit:
   - 分别 commit 或一起, message 描述结构 + node 索引 + 模板来源
5. **不要 push**(我会自己 push)。
6. 把结果写到 `trainverify/RESULT_G283_54.md`: 每个 goal 的 commit hash、是否 0 sorry、踩的坑。

## 纪律
- 改核心文件(Denote.lean / GeneratedData.lean)→ 禁止。只新增 Bridge + 改 MainTheorem 的 sorry 行 + 改 gen 脚本。
- helper 引理名不确定 → `grep -rn` 在 denote/ 下确认真实名字, 不要编。
- native_decide 报错说 node 索引不对 → 重新探针(用 `#eval (List.range pm.nodes.length).filterMap ...` 模式)核对。
- 卡住超过合理尝试 → 在 RESULT 文件写清卡在哪、错误信息, 不要无限循环。
