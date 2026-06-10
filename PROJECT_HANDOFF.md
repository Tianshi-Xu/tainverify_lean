# TrainVerify Project Handoff

本文档面向长期推进 TrainVerify Lean 证明工作的同学。目标是能定位问题、修复生成器/语义定义，并逐步推进自动化证明流程。

## 1. 项目目标

TrainVerify 的目标是验证单卡计算图（SM, single-machine / reference graph）和并行计算图（PM, parallel graph）在数学语义上一致。

当前主线不是运行真实训练，而是把 nnScaler / Verdict 生成的计算图转换成 Lean 中的图声明，然后用 `trainverify/denote/Denote.lean` 里的算子语义解释这些图，最终证明 SM 和 PM 的 observable tensors 满足 coarse lineage/equivalence 关系。

简单说：

1. Python 侧生成或读取两个计算图：一个参考图，一个并行图。
2. `Verdict/graph_to_lean.py` 把两个图转换为 Lean 数据：`GraphDecl`、shape env、init goals、per-goal slices、pattern skeletons。
3. Lean 侧 `denote/Denote.lean` 提供张量、算子、通信 primitive、图执行和 lineage 语义。
4. 每个 `Goal_*.lean` 或 `SegmentPattern_*.lean` 证明某一类输出/梯度在 SM 与 PM 之间一致。

## 2. 代码结构

关键路径：

- `Verdict/graph_to_lean.py`: 计算图到 Lean 的主转换脚本。很多“证明失败”其实是这里生成错了节点、参数、shape 或切片边界。
- `trainverify/denote/Denote.lean`: Lean 侧 denotational semantics。所有 op 的数学定义和 `evalOp` 分发都在这里。
- `trainverify/denote/GeneratedData.lean`: 默认生成文件。
- `trainverify/denote/gpt_ly4_segments/`: GPT ly4 分段生成结果。
- `trainverify/denote/gpt2_small_ly12_segments/`: GPT2-small ly12 分段生成结果，规模很大，容易触发 Lean codegen/recursion/stack 限制。
- `trainverify/bug.md`: 已知生成器/语义 bug 的审计记录。
- `trainverify/lakefile.toml`: Lean 工程根在 `trainverify/`，不是 repo 根目录。

常用命令需要在 `trainverify/` 下运行：

```bash
cd /data/home/xts/code/tainverify_lean/trainverify
lake build denote.Denote
lake build denote.gpt_ly4_segments.GeneratedData
lake build denote.gpt2_small_ly12_segments.GeneratedData
lake build denote.gpt2_small_ly12_segments.Goal_3
```

## 3. 核心工作流

### 3.1 生成计算图

参考根目录 `README.md`。一般流程是先准备 conda 环境和 nnScaler，然后运行 `genmodel/` 或已有 pickle 文件，得到 SM/PM 两个执行计划。

典型输入文件位于：

```text
genmodel/mgeners/*.pkl
```

例如 gpt2-small ly12 对应：

```text
genmodel/mgeners/gpt_mgener_dp1_pp1_tp1_nm1_gbs1_dim768_ly12_h12_hi768_sq1024_voc50257.pkl
genmodel/mgeners/gpt_mgener_dp1_pp1_tp4_nm1_gbs1_dim768_ly12_h12_hi768_sq1024_voc50257.pkl
```

### 3.2 生成 Lean 文件

主入口是：

```bash
python Verdict/graph_to_lean.py \
  --sm-pkl <single.pkl> \
  --pm-pkl <parallel.pkl> \
  --out trainverify/denote/<target>/GeneratedData.lean \
  --split-goals \
  --goals-out-dir trainverify/denote/<target>
```

如果开启 segment pattern，还会生成 `Pattern_*.lean`、`SegmentPattern_*.lean`、`Instances.lean` 等辅助文件。

### 3.3 编译语义和生成数据

先构建核心语义：

```bash
cd trainverify
lake build denote.Denote
```

再构建目标生成数据：

```bash
lake build denote.gpt_ly4_segments.GeneratedData
```

对大文件，优先构建具体 goal，而不是整包全量构建：

```bash
lake build denote.gpt2_small_ly12_segments.Goal_3
lake build denote.gpt2_small_ly12_segments.Goal_309
```

### 3.4 写证明

证明通常按三层推进：

1. 先证明局部算子/通信 primitive 的 shape 和 value lemma。
2. 再证明单个 `Goal_*.lean` 的 SM/PM 图等价。
3. 最后抽象为 `Pattern_*.lean` 或 `SegmentPattern_*.lean`，复用到重复结构。

注意：`GeneratedData.lean` 和 `Goal_*.lean` 是自动生成物。手工 patch 可以用于救急和确认 bug，但长期应把修复落回 `Verdict/graph_to_lean.py` 或 `Denote.lean`，再重新生成。

## 4. 当前困难

### 4.1 错误来源跨 Python 和 Lean

证明失败不一定是 Lean proof 写错。常见原因包括：

- Python 生成器漏了 op 参数。
- Python 生成器把同名 op 用在了语义不同的并行模式上。
- Lean `evalOp` 没有分发某个生成器已经 emit 的 op。
- shape env 或 init goal 选错，导致后续目标在错误边界上证明。
- 大型生成文件触发 Lean 的递归深度、代码生成或 stack 限制。

定位时要先判断“目标是否数学上为真”。如果生成图语义本身错了，继续写 proof 只会浪费时间。

### 4.2 算子语义和并行策略耦合紧

同一个高层算子在不同并行策略下可能需要不同语义参数。例如 embedding：

- hidden-sharded token embedding：每个 rank 有完整 vocab 的 hidden slice，输出后 gather。这里 plain `FW_embedding` 是对的。
- row/vocab-sharded embedding：每个 rank 只有 vocab row shard，输出后 AllReduce。这里必须带 row offset，否则 rank 会用 global id 直接索引 local shard。

这类问题需要同时看：weight shard shape、embedding 输出的 consumer、通信 primitive、backward 对应节点。

### 4.3 生成文件巨大

`gpt2_small_ly12_segments/GeneratedData.lean` 约 18k 行，完整 `lake build` 可能因为 Lean codegen 栈溢出失败。即使前端语义没问题，生成 `.c`/`.olean` 时也可能失败。

处理原则：

- 优先构建 `denote.Denote`。
- 优先构建具体 `Goal_*.lean` 或较小 segment。
- 对完整大文件，只把它作为静态检查和数据源，不要默认要求每次全量 codegen 通过。
- 必要时把巨大 list/definition 拆分成 chunk，或将不需要执行代码的声明改为更适合 Lean 编译器的形式。

### 4.4 证明性能脆弱

Lean 证明很容易因为 `simp` 展开太多定义而慢到不可用。项目已有经验：

- 能直接引用 lemma 就不要大范围 `simp`。
- 避免 `simpa [big_def] using h` 展开大定义。
- 新 lemma 必须放在依赖它的 lemma 之后。
- 三元组目标用 `refine ⟨?_, ?_, ?_⟩`。
- `lake build module.File` 通常比直接 `lake env lean` 更适合日常增量验证。

## 5. 常见问题与解决方案

### 5.1 `Unknown identifier`

原因：lemma 定义顺序错，或 import 目标不对。

解决：

- 把新 lemma 移到依赖它的 lemma 之后。
- 检查文件 module path。Lean 工程根是 `trainverify/`。
- 用 `lake build denote.Denote` 先确认核心文件可见。

### 5.2 `evalOp` fallback 导致输出是默认值

现象：生成图里有某个 op，但 `Denote.lean` 的 `evalOp` 没有 branch。`applyNode` 会把 empty output list zip 到 outs，结果目标 tensor 没被写入，后续读到默认/zero tensor。

解决：

1. `rg -n "OpName.<name>" trainverify/denote` 看生成器是否 emit 了该 op。
2. `rg -n "<name>" trainverify/denote/Denote.lean` 看 `evalOp` 是否分发。
3. 若缺失，补上数学语义分支和必要 unfolding lemma。

已知例子：`OpName.BW_multiref` 应解释为所有输入梯度的 `tensorSum`。

### 5.3 embedding goal 数学上不成立

现象：position embedding / vocab-sharded embedding 的 PM 侧使用 plain `FW_embedding`，然后 AllReduce；goal 无法证明。

原因：plain embedding 没有 row offset 和 range check，rank 会用 global row id 直接索引 local shard。

解决：

- row/vocab-sharded forward 节点需要 `params := [rank * shard_rows]`，由 `fw_embedding_offset` 解释。
- backward 节点也需要同样 offset，由 `bw_embedding_offset` 解释。
- hidden-sharded token embedding 不要加 offset。
- 生成器侧判据应优先看 FW embedding 输出是否被同一个 `AllReducePrim` 汇合；如果输出走 gather/all-to-all hidden 分片路径，则保持 plain。

### 5.4 AllToAll / Chunk / AllGather 参数错

现象：shape 对不上，或者 value lemma 里 index 映射方向反了。

解决：

- 对 `AllToAllPrim`，确认 `params := [idim, odim]` 与 `allToAllPrimWithDims` 的解释一致。
- 对 `ChunkPrim` 和 `AllGatherPrim`，用 input/output shape 反推 split/gather dim。
- 写小样例手算 shape，不要直接在大目标里调 proof。

### 5.5 `maximum recursion depth reached`

原因：生成文件过大，Lean elaboration/codegen 处理巨大 list 或大 definition 时超过 `maxRecDepth`。

解决：

- 先在生成文件设置 `set_option maxRecDepth 100000`。
- 如果仍失败，构建更小的 `Goal_*.lean`。
- 长期方案是修改 generator，把巨大 list 拆成 chunk，避免一个 definition 内嵌数千项。

### 5.6 `Stack overflow detected. Aborting.`

原因：Lean codegen 对巨大 generated definitions 栈溢出，常见于 gpt2-small ly12 全量 `GeneratedData.lean`。

解决：

- 不要把完整大文件全量构建作为每次 proof 的必要 gate。
- 构建具体 goal 或 segment。
- 长期要拆分 `pm`、`pmInitShapes`、`goal_*`、`initGoals` 等巨大声明，或生成多个小模块。

### 5.7 proof 很慢或超时

解决：

- 减少 `simp [big_def]`。
- 把复杂 shape/value 事实拆成小 lemma。
- 对固定 shape 用专门 lemma，不要让 `simp` 搜索整个图语义。
- 先证明 shape，再证明 value；不要在一个 theorem 里同时展开全部图执行。

### 5.8 生成物和生成器不一致

现象：手工修了 `Goal_*.lean`，但下一次生成又丢失。

解决：

- 所有可复现 bug 必须回写到 `Verdict/graph_to_lean.py` 或 `Denote.lean`。
- 手工 patch 只用于快速验证和 unblock。
- 重新生成后用 `git diff` 检查是否只变了预期区域。

## 6. 接手者建议流程

如果遇到一个新失败 goal，按这个顺序处理：

1. 读失败的 `Goal_*.lean`，列出 SM/PM 节点和目标 tensor。
2. 在 `GeneratedData.lean` 中找同一组节点，确认不是切片生成特有问题。
3. 看 PM 侧每个 op 的 `params`、shape、consumer 通信 primitive。
4. 在 `Denote.lean` 找对应 op 语义和 `evalOp` branch。
5. 判断目标是否数学上为真。
6. 若数学上为假，先修 generator 或 op semantics。
7. 若数学上为真，再补 lemma/proof。
8. 修完后至少跑：

```bash
cd /data/home/xts/code/tainverify_lean/trainverify
lake build denote.Denote
lake build <具体失败模块>
```

对超大模块，允许记录 Lean codegen 限制，但必须说明局部模块是否通过。

## 7. TODO: 自动化证明流程

项目下一阶段最重要的 TODO 是建立自动化证明流程，减少每次人工排查 generator bug 和 Lean proof 性能问题的成本。

目标流程：

1. 自动生成 SM/PM 图和 Lean 文件。
2. 自动静态审计生成图：检查 op 是否都被 `evalOp` 分发、arity 是否匹配、shape 是否与 op 语义一致、embedding 是否正确区分 row-sharded 与 hidden-sharded。
3. 自动为每个 goal 选择 proof strategy：base op、communication op、linear/embedding/layernorm/backward segment 分开处理。
4. 自动生成局部 lemma skeleton，而不是只生成 `sorry` theorem。
5. 自动按依赖顺序构建：先 `Denote`，再小 goal，再 pattern，再 segment，最后才尝试大 `GeneratedData`。
6. 自动收集失败类型并分类：generator bug、missing semantics、shape mismatch、proof timeout、Lean compiler/codegen limit。
7. 自动输出修复建议：需要改 generator、需要补 op semantics、需要拆大模块、还是需要新增 proof lemma。

验收标准：

- 一个新模型配置生成后，脚本能给出可读的 pass/fail 报告。
- 常见错误不需要人工从 18k 行 Lean 文件里 grep 定位。
- 对无法全量 codegen 的大模块，流程能自动 fallback 到 per-goal / per-segment 构建。
- 每个失败 goal 都能关联到最小 SM/PM 子图和可能的问题类别。
