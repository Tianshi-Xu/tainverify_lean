# 远程分支收敛记录（2026-09-14）

仓库：`https://github.com/Tianshi-Xu/tainverify_lean`。审查时集成目标为 `integration/trainverify-forward-backward`，源码/报告 tip 为 `54cc9cf57f5b65b66ce7da932e9a85d15badce1a`。

用户选择：**删除已吸收的工作分支，保留 archive 分支**。本次没有合并或更新 `main`，没有强行合回旧证明或另一个编译器，也没有用 `ours` merge 制造已吸收历史。

## 结果

初始远程共 11 个分支；删除 2 个已完整位于集成历史中的工作分支后，剩余 9 个。剩余分支内容没有需要立即整头合并的已验证遗漏。此结论不等于所有旧分支已合入，也不等于所有实现逐项语义等价。

### 已删除：内容原本已在集成历史中

- `fix/yoco-release-registry-layering`：`9cfbfc78048e15961418b84b4595ef38baea619e`，与当时远程 main 同 tip。
- `regen/yoco-a04b-9a1be1d`：`de30b89ffd9d67da37cd4e26bea1d534a46e198b`。

删除前逐项确认远程 SHA 未漂移、tip 为已推送集成提交的祖先、没有相应 open PR；使用 exact-old-SHA lease 的原子删除，再读取远程 refs 确认。提交仍可从远程集成历史恢复，不涉及强制改写提交历史。

### 保留：主线与集成

- `main`：仍为 `9cfbfc78048e15961418b84b4595ef38baea619e`。
- `integration/trainverify-forward-backward`：保留本地新增成果；本记录的文档提交会使该分支前进，功能源码不变。

### 保留：两个尚未合入的早期编译原型

- `feat/generic-proof-compiler`：`ecf59f7d5f3bb0ce36d36631e2df5a28b46334aa`。
- `feat/generic-proof-kernel-checker`：`b2a0fa94a03e8c160d53cff0bc2a6ba0a7337945`，包含前一个 tip。

两个分支合计覆盖 13 个新增路径。旧成果包含 typed JSON IR、证书 DAG 验证及 unary-map 条件式 Lean 组合，不能说没有价值；但它们未接当前 source/model authority、faithful evaluator、closed segments 和完整发布合同。当前 bridge_emitter 已用另一演进路线承担主要职责。

未找到它们曾合入再被删除的明确历史证据，也没有证明所有旧行为已逐项吸收，因此**未删除这两个分支**。整头合入将恢复另一套独立编译路线；旧 kernel CLI 缺少最终 axiom 审计，还有 Python CI lane 的 Lean 依赖接线风险。本次不执行旧测试/编译，也不把静态审查写成 kernel PASS。将来如需旧负控的测试性质，应明确差集并移植到当前接口，而非恢复整个包。

### 保留：五个 archive 分支

- `archive/gpt-goal107-finding-20260510`：`7037676be95233682ce9a7b28f7f0617d8a11b6b`。保留旧 BW embedding 缺 offset 导致重复 shard 的研究注记；原文件仍有 sorry，不是完整 kernel 反例。当前 `trainverify/denote/gpt_ly4_regen/Goal_107.lean` 已使用四个 offset 及对应证明，不恢复旧 Pattern_53。
- `archive/gpt2-decycle-pre-cleanup-20260524`：`f646343951bcbffebb015f04d621740997c6a89d`。135 个变更路径已分组审查；其中大量修改只新增 sorry，含旧提取公理、stub 和 1GB 栈参数。当前已有大部分数学替代，不恢复退役证明架构。零宽 row-parallel dX 声明域可作将来的独立小适配研究，不是已确认当前 GPT 正维度实例缺失。
- `archive/replication-criterion-spike-20260715`：`a015b772564be3415282b410c87b0c7f9e396f4d`。保留研究原则和失败实验；不能合入 immediate-producer whitelist，更不能从“无法证明 replicated”自动改判为 gather。
- `archive/yoco-fidelity-pre-cleanup-20260802`：`a5dd2cd052dedbff30eabf96929d451656aa675f`。已是当前集成祖先，仍按用户选择保留 archive。
- `archive/yoco-router-shapes-workerD-20260706`：`239820ab488d7ca68a53b3b1029ef5fa14642f17`。八个 helper 已逐字继承，1116 个 hs 名称/输出 shape 及两条 rank shape 证明已有对应；不恢复旧未完成 assembly 或旧 public statement，保留归档溯源。

## 后续交接风险：旧 emitter replication 判据尚未关闭

静态确认 `Verdict/graph_to_lean.py:2982–2989` 的旧 goal emitter 仍以 piece 数和 shape 相等推断 `replicated`；`2884–2890` 附近另有相关形状启发式。要求文档已强调 value/ownership provenance，不代表这些旧推断已经完成迁移。

父审查提取并执行了第一处**原生产赋值 AST**：SM shape `[2]`、两个 PM shape `[2]` 时，判据返回 `True`；配上不同的 PM 值 `[1,0]`、`[0,1]`，可见该局部判据本身没有建立值复制关系。该观察只针对原谓词，**没有运行真实 capture、完整 CLI、public admission 或 Lean 假定理反例**，不能推导所有现有已验收证明错误。

这项风险属于旧 exporter/关系推断边界，不能用已拒绝的 spike 白名单“修复”，也不能外推最新 source-bound runtime canonical 的复本事实没有通过核验。后续应沿真实 authority/调用链单独定位，unknown 保持拒绝或 finding；本次分支整理不修改生产代码。

## 证据与未执行项

本机证据根：`/home/v-zhouziyu/trainverify-audits/remote-branch-consolidation/20260914T091810Z/`。

- `inventory.json`、`unabsorbed-ancestry.json`：初始完整远程清单、祖先/patch 差异。
- `compiler-review/`、`gpt-archive-review/`、`misc-archive-review/`：逐分支/逐路径来源、替代关系、保留理由。
- `first-retirement.json`、`FINAL.json`：删除与保留的逐项 disposition、远程读回。
- `replication-predicate-observation.json`：局部生产谓词观察及严格范围声明。

本次审查不认证任何旧 archive 的 kernel 完整性；没有执行新训练、capture、全库 build 或恢复已退役源码。远程分支数减少来自清理已吸收引用，不是假装所有旧 head 都已合并。
