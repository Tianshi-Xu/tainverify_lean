# 当前交接入口

本项目当前处于**成果整理与交接维护阶段**。暂停新增算子、推进后续 frontier（已证明值关系的边界）和 canonical attachment（接入默认生成链）；下面列出的缺口是边界说明，不是自动继续开发的任务队列。

## 先看结论

TrainVerify 比较单模型参考图 **SM** 与分布式图 **PM**。最新收妥的增量是原始 score division adapter：在相同 SM/PM 完整运行和初始参数关系假设下，证明全局输出形状、每个局部输出形状及跨 rank 的重建关系。它**不是整模型等价证明，也不是成功执行整张图的共同 witness**。

需要区分两个边界：

- **默认 canonical 路径**仍到 Q/K score matmul 和 PM AllToAll(1→3)。后续 division 在该路径中仍未附着；`RuntimeLineageBlocked` 保留。
- **独立调用的 score division adapter**已完成 source、actual saved-source、Lean kernel 和完整 mixed joint 验收，代码已经收进本地 integration。它没有被接入默认 canonical 路径。

“独立验收通过”和“默认入口已接入”不是同一件事；也不要把旧状态中的 inventory-only 理解为 division 代码和证明仍未实现。

## 唯一修改入口与版本

只在主 integration checkout 工作，分支为 `integration/trainverify-forward-backward`。源码入口：

- [division renderer](../Verdict/runtime_frontier_score_div_values.py)
- [完整测试](../scripts/tests/test_runtime_frontier_score_div_values.py)

已验收源码 commit：`05584e60f6216b153175c3f49ea1754a7f64d07a`。本次整理在该代码上只追加交接文档与数据索引。精确两文件指纹及证据目录提示在 [机器可读索引](handoff/score-division.json)。工作树和集成状态以 Git 为准，不以私有候选目录的名字为准。

证据目录里的 `acceptance/source`、`acceptance/source-v2` 及 worker source 都是**冻结的历史/验收快照，不是第二个开发入口**。其中 `source-v2` 是通过验收的来源；`source` 是较早失败候选。保留它们是因为 receipts 仍引用其源码路径，不意味着还需要挑一个目录继续开发。

## 已验证的范围

- 最终 Python：**146 项新 suite + 1 项前驱 public tracer，共 147 passed，零失败/错误/跳过**。两个不相交批次的 collected IDs、JUnit、源码 hashes 完整核对。早先 139 项结果是历史版本，不能与最终结果相加。
- actual2：从既有受信任 captures 回放，**5 个原始 read equations、2 个完整 unit facts、6 行 frontier**，没有 recapture。12 个 public predecessors 各调用一次，六个 authority 对象身份不变。
- Lean：**7 个新声明和六行 mixed joint**通过 kernel，只依赖 `propext`、`Classical.choice`、`Quot.sound`（kernel3）。V 保留每副本 equality 和 `gather_axis=None`，两条 residual 的完整事实及原历史保留。
- **12 个前驱生成片段逐字不变；154 个旧 full Lean Expr 合同完全一致**。除法 helpers 的 44-module source/object/import closure 已认证，既有对象复用，没有为交接重编它们。

Renderer 返回的 `proof_admissible`、`kernel_value_proved` 等 flags 仍为 false：renderer 每次面对新的输入只生成未编译文本，不能根据某次外部验收永久翻旗。外部 receipts 证明的是那个**精确源码与输入绑定**下的条件合同，不是任意未来 render 的完成状态。

## 从哪里核验

[运行手册](score-division-runbook.md)先给只读核查，再给可选的昂贵重放。外部证据根由 `TV_EVIDENCE` 指定，机器可读索引提供此机器上的位置提示。

优先阅读这些相对路径，不必遍历全部日志：

1. `result.json`：该切片验收总索引；`REPORT.md`：验收阶段摘要。两者是冻结的验收快照，其中“未合入 integration”描述的是验收当时，不覆盖本次 Git 收尾状态。
2. `acceptance/acceptance.json`、`acceptance/actual-source-audit.json`：actual/kernel/joint 结论、原节点与前驱/共同上下文比对。
3. `acceptance/actual2/FreshScoreDiv.lean`、`detail.json`、`world-binding.json`：完整生成源码、fullrefs、形状、标量、后缀与输入 authority。
4. `acceptance/kernel-div/result.json`、`acceptance/kernel-joint/result.json`：实际命令、源/对象/import/log hashes、axiom 查询结果。
5. `acceptance/old-contract-comparison.json`、`acceptance-final-reconciliation.json`：旧完整合同保留与最终测试覆盖。

[SHA-256 清单](handoff/score-division.sha256)覆盖本切片的选定验收文件；它不是所有外部依赖的自包含打包。外部依赖另由显式 layout 验证。**仓库 clone 本身不包含 captures、nnScaler 内部 wheel 和所有已接受 Lean 缓存。**

## 历史材料怎么处理

- `acceptance/actual1`：真实 SM softmax inventory 缺口导致的失败，随后在原两文件内修复；不是数学反例，也不是当前结果。
- `python-result-v1.json`、`PYTHON_REPORT_v1.md`、`final-*`：139 项的旧 Python checkpoint。
- `focused-history-cover*`、`red-owned*`：中断/部分结果，不能充当完整覆盖。
- `closure-controller.json` 与 `report-revalidation.json`：历史报告汇总失败及恢复，不是一次新的测试或 kernel 验收。
- 外部根中的 `*.py`：冻结运行记录，可能有固定路径、一次性输出名和旧入口。**不要把它们当成受维护 CLI 再执行。** 使用 Git 中的 `trainverify.frontier_replay`、`artifact_tools`、`artifact_contracts`。

本次不移动、删除或改写 hash-bound 原始证据。未来迁移必须使用显式路径映射并维持原 expected hashes；缺文件应报错，不能跳过或重算 pins 使其通过。

## 明确暂停的工作

原始 PM AA(3→2)、SM/PM softmax 值关系、后续 `probabilities @ V` 和 saved-primal 链仍未推进；当前下一消费者只是 inventory。canonical attachment、完整包预算/发布门禁、whole-model/public completion、共同完整执行 witness 和 Torch/CUDA refinement 也不在本次交接整理范围内。

其他证明路线与历史贡献见 [架构](ARCHITECTURE.md)、[冻结的研发交接报告](HANDOFF_2026-09-14.md)和 [workstream ledger](../WORKSTREAMS.md)。这些路线的 evaluator、源码 authority 和 axiom policy 不可混用。本次 division 验收不更新历史 YOCO/Whole 覆盖率，也不解决 legacy replication heuristic。
