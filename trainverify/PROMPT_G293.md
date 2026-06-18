# Task: 证 TrainVerify bridge — goal_293 — 并 wire 进 MainTheorem

工作目录: `/home/argustest/.openclaw/workspace/tainverify_lean/trainverify`
所有相对路径都相对此目录。仓库根是 `/home/argustest/.openclaw/workspace/tainverify_lean`。
模型架构验证项目, bridge 是 "cut → full" 的 frame 包装。**纯模板填空, 无创造性**。

## 背景: bridge 是什么
每个 `Goal_N.lean` 已有 `prove_goal_N_cut`(0 sorry, 假设 prereq 成立证局部等价)。
bridge(`GoalNBridge.lean`)用拓扑序上已证的 `goal_M_intermediate` 消掉 cut 的假设,
产出无条件 `goal_N_cut_to_full` + `goal_N_intermediate`。照已有 bridge 抄, 只换 tid/node/op/shape/prereq。

## goal_293 结构(模板 = `Goal285Bridge.lean`)

goal_293 是 `FW_multiref params=[3]` 节点的**第三输出(THIRD output)**, **无 collective tail**,
multi-tps gatherDim=1。结构上跟 goal_285(第一输出 first-out, 无 collective)**几乎一样**,
唯一区别是取第三输出而非第一输出(用不同的 helper, 且 helper 需要两个不等式假设)。

### 精确节点 / tid(已从 `Goal_293.lean` 核对)
- **SM**: node **61** = `FW_multiref(640) → [1004, 1008, 1012], params := [3]`, 取**第三输出 1012 = 640**。 shape [1,8,32]
- **PM**: nodes **396/397/398/399** = `FW_multiref(2229+r) → [3607+, 3609+, 2313+r], params := [3]`,
  各取**第三输出 2313/2314/2315/2316** = 各 rank 输入 2229/2230/2231/2232 的恒等。 各 [1,2,32]
  - rank0: `FW_multiref(2229)→[3607,3609,2313]` 取 2313
  - rank1: `FW_multiref(2230)→[3617,3619,2314]` 取 2314
  - rank2: `FW_multiref(2231)→[3627,3629,2315]` 取 2315
  - rank3: `FW_multiref(2232)→[3637,3639,2316]` 取 2316
  - ⚠ **无 AllGather / AllToAll**。multiref 三输出, 取第三个直接就是输入恒等。
- goal_293 LineageGoal: `ts:=1012, tsShape:=[1,8,32], tps:=[2313,2314,2315,2316], tpShapes:=4×[1,2,32], gatherDim:=1`
- **输入 640** 来自 goal_55 (dim1-gathered [1,8,32], PM tps 2229-2232 [1,2,32])。
- **prereqs**: goal_2..55 + 257,259,...,285 (odd) = **69 个**。
  **完全等于 goal_289_prereqs / goal_291_prereqs**(去 `Goal_293.lean` 里 `goal_293_prereqs` 核对精确顺序;
  已确认与 goal_289 的列表逐字相同, 只差名字 289↔293)。

### 关键 helper(已 pre-baked 在核心 Denote.lean, **不要改 Denote.lean**)
取第三输出的 helper 已存在:
```
theorem applyNode_fw_multiref3_third_out_g293
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 : Tid)
    (h13 : ¬ t1 = t3) (h23 : ¬ t2 = t3) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2, t3], params := [3] } t3 = s xTid
```
⚠ 它需要**两个不等式假设** `h13` `h23`(t1≠t3, t2≠t3), 用 `(by decide)` 或 `(by native_decide)` 提供。
goal_285 用的 `applyNode_fw_multiref2_first_out` **不需要**不等式假设 — 这是改写时唯一要小心的地方。

(还有 `applyNode_fw_multiref3_pass_g293` 处理读取异于三输出的 tid, 一般用不到, 知道存在即可。)

## 做法
1. `cp denote/gpt_ly4_regen/Goal285Bridge.lean denote/gpt_ly4_regen/Goal293Bridge.lean`
2. **完整读一遍** Goal285Bridge.lean, 理解它如何取第一输出(989=637, node 59 / PM 388-391)。
   goal_293 改成取**第三输出**(1012=640, node 61 / PM 396-399)。
3. **import 改**: Goal285Bridge import 的是 `Goal54Bridge` + `Goal283Bridge` + `Goal_285`。
   goal_293 需要的上游是 **goal_55**(输入 640 来自它)。改成 import:
   - `import denote.gpt_ly4_regen.Goal55Bridge`(提供 goal_55_intermediate)
   - `import denote.gpt_ly4_regen.Goal285Bridge`(提供 goal_285_intermediate; goal_293 prereq 含 goal_285)
   - `import denote.gpt_ly4_regen.Goal_293`
   - ⚠ goal_293 的 hInitCut 需要 hg2..hg55 + hg257..hg285 全部 intermediate。这些经由 import 链传递性可见
     (Goal285Bridge 已 import 了 goal_283…一路往前)。先按上面三个 import 试编译, 缺谁补谁的 Bridge import。
4. **hInitCut helper**: goal_293 的 prereq 列表 = goal_289 的逐字相同。
   **复用 `goal_289_hInitCut_helper`**(在 Goal289Bridge.lean 里定义, line ~110)。
   - 即 import `Goal289Bridge`, 然后 `hInitCut` 那里调
     `goal_289_hInitCut_helper Ssm Spm hinitC hg2 ... hg55 hg257 ... hg285`(参数顺序照 Goal289Bridge line ~335 那段抄)。
   - ⚠ 前提: `goal_293_cut_initGoals` 必须与 `goal_289_cut_initGoals` 定义相等(因 prereq 逐字相同, 应当 defeq;
     若 Lean 报类型不匹配, 退路是自己写 `goal_293_hInitCut_helper`, 照 goal_289 的 helper body 复制改名)。
5. **全文替换**(从 285 模板 → 293):
   - `285` → `293`(所有 `goal_285*` / `sm_goal_285*` / `pm_goal_285*` / `_285_` 标识符)
   - SM: node `59` → `61`; tid `989` → `1012`; `637` → `640`; multiref 其它输出 `[989, 993]` → `[1004, 1008, 1012]`
   - PM: nodes `388/389/390/391` → `396/397/398/399`; 输出 tid `2225/2226/2227/2228` → `2313/2314/2315/2316`;
     输入 tid `2201/2202/2203/2204` → `2229/2230/2231/2232`;
     PM 各 rank 的三输出 outs 改成 `[3607,3609,2313]` / `[3617,3619,2314]` / `[3627,3629,2315]` / `[3637,3639,2316]`
   - **helper 调用**: 把所有 `applyNode_fw_multiref2_first_out`(取第一输出, 无 hne)
     换成 `applyNode_fw_multiref3_third_out_g293 _ _ _ _ _ _ _ (by decide) (by decide)`(取第三输出, 带两个不等式)。
     - ⚠ 注意参数个数/占位: helper 签名是 `(g s rank xTid t1 t2 t3) (h13) (h23)`。
       rw 时一般 `rw [applyNode_fw_multiref3_third_out_g293 (h13 := by decide) (h23 := by decide)]`
       或显式给 `(by decide) (by decide)`。先看 285 里 `rw [applyNode_fw_multiref2_first_out]` 是怎么写的, 照搬结构补不等式参数。
   - SM/PM 的 `rw [show sm.nodes[59]... = {... outs := [989, 993], params := [2]} ...]` 这类 `show` 块:
     改 node 索引 61、outs `[1004,1008,1012]`、params `[3]`。PM 同理改 396-399 + 三输出 + params[3]。
6. **InitShapes 顺序**: 读 `Goal_293.lean` 里 `sm_goal_293InitShapes` / `pm_goal_293InitShapes` 的**确切顺序**:
   - SM: `[(640, [1,8,32])]`(只有一个! 注意 285 的 SM 是 637; 293 的 hSM rcases 只有 1 个分支)
   - PM: `[(2229,[1,2,32]),(2230,[1,2,32]),(2231,[1,2,32]),(2232,[1,2,32])]`
   - hSM/hPM 的 rcases 分支按该顺序 exact 对应 shape 假设。从 hg55(不是 hg54!)提取 640 / 2229-2232 的 shape。
     ⚠ 285 是从 hg54 提取 637 的 shape; 293 要从 **hg55** 提取 640 的 shape(因为 640 是 goal_55 的输出 ts)。
     看 goal_55 LineageGoal 的 ts/tps 是不是就是 640 / 2229-2232 来确认提取方式(`have h := hg55.1; simp only [goal_55] at h; exact h` 之类)。
7. **frame 自指**: 285 有 `sm_frame_989_self` + `pm_frame_2225_self..2228_self`。
   293 对应 `sm_frame_1012_self` + `pm_frame_2313_self..2316_self`, 内部用第三输出 helper。
8. **wire**: 打开 `denote/gpt_ly4_regen/MainTheorem.lean`:
   - 在 import 区(其它 `import ...GoalNBridge` 旁)加 `import denote.gpt_ly4_regen.Goal293Bridge`。
   - line **911**: `theorem goal_293_full : goal_293_stmt := by sorry  -- cut-form not yet proven`
     改成 `theorem goal_293_full : goal_293_stmt := goal_293_cut_to_full prove_goal_293_cut`
     (照 line 903 `goal_285_full` / line 907 `goal_289_full` 的写法)。

## 验证 goal_293
1. 编译 bridge(⚠ 必须**从 trainverify 目录**用 lake build module 名, 不能 `lake env lean <path>`):
   ```
   cd /home/argustest/.openclaw/workspace/tainverify_lean/trainverify
   lake build denote.gpt_ly4_regen.Goal293Bridge
   ```
   → "Build completed successfully", 0 error。
2. `grep -c sorry denote/gpt_ly4_regen/Goal293Bridge.lean` → **0**
3. `git diff bc19002 -- denote/gpt_ly4_regen/Denote.lean`(在仓库根跑) → **空**(没动核心语义文件)。
4. #print axioms 检查: 临时在 Goal293Bridge.lean 末尾加 `#print axioms goal_293_intermediate`, 重编一次,
   确认**无 `sorryAx`**(允许的: propext / Classical.choice / Quot.sound / Lean.ofReduceBool /
   Lean.trustCompiler / applyNode_* 系列 / erfFn / expFn / sqrtFn / piScalar / scalarToNat 等)。看完**删掉**这行。
5. 整体 MainTheorem 编译(确认 wire 没破坏别的):
   ```
   lake build denote.gpt_ly4_regen.MainTheorem
   ```
   → Build completed successfully。`goal_293_full` 不应再出现在残余 sorry 警告列表里
   (其它未证 goal 如 goal_58+ 的 sorry 警告是正常的, 别管)。

## 提交
1. `git add` 新文件 `denote/gpt_ly4_regen/Goal293Bridge.lean` + 改过的 `denote/gpt_ly4_regen/MainTheorem.lean`。
2. commit, message 描述结构 + node 索引 + 模板来源, 例如:
   `prove goal_293 bridge (FW_multiref params=[3] THIRD-output, no collective, multi-tps gatherDim=1; SM node 61 FW_multiref(640)->[1004,1008,1012] take third 1012=640; PM nodes 396-399 4xFW_multiref(2229+r)->[...,2313+r] take third 2313-2316 = each rank input identity, no AllGather; input 640 from goal_55 dim1-gathered [1,8,32] tps 2229-2232 [1,2,32]; template Goal285Bridge (first-out no-collective) adapted to THIRD output via applyNode_fw_multiref3_third_out_g293 (needs h13/h23 by decide); reuse goal_289_hInitCut_helper (identical 69 prereqs [2..55,257-285 odd]); unblocked by goal_55, unlocks goal_58) + wire MainTheorem`
3. **不要 push**(我会自己 push)。
4. 把结果写到 `denote/../../RESULT_G293.md`(即 `trainverify/RESULT_G293.md`):
   commit hash、是否 0 sorry、#print axioms 结果、踩的坑、是否复用了 goal_289_hInitCut_helper(还是自己写了)。

## 纪律
- 改核心文件(`Denote.lean` / `GeneratedData.lean`)→ **禁止**。只新增 `Goal293Bridge.lean` + 改 MainTheorem 的 import+goal_293_full 行。
- helper 引理名不确定 → `grep -rn` 在 `denote/` 下确认真实名字, **不要编**。
- `native_decide` 报 node 索引不对 → 用 `#eval` 探针核对 `pm.nodes[396]` / `sm.nodes[61]` 的真实内容再改 show 块。
- 第三输出 helper 的两个不等式参数一定要补(`by decide`), 这是跟 285 模板最大的差异, 漏了会编译失败。
- 卡住超过合理尝试(比如 hInitCut helper 复用类型不匹配且自写也不通)→ 在 `RESULT_G293.md` 写清卡在哪、完整错误信息, **不要无限循环**。
