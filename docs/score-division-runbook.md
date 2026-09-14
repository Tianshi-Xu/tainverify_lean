# Score division 交接运行手册

先读[当前交接入口](HANDOFF.md)。默认任务是验证已有成果能被找到和复用，**不是继续开发或重跑所有证明**。以下命令面向 Bash/Linux；输出一律进入新的私有目录。

## 1. 环境与路径

此 checkpoint 的验证环境为 Python 3.11.13、pytest 9.1.1、nnScaler 0.9+internal.1、Torch 2.6.0+cu124、Lean 4.32.2。它们是已观察配置，不是任意版本兼容承诺。nnScaler 内部依赖获取方式及工具入口见 [Development](../DEVELOPMENT.md)。不要将仓内 `nnscaler_genmodel` 当成当前安装包。

在主 integration checkout 内运行。三个路径可由调用者预先设置；否则读取[索引](handoff/score-division.json)中此机器的提示。换机器时必须调整路径/layout，不能修改旧 receipts 或其 expected hashes 来消除缺文件错误。

```bash
set -euo pipefail
TV_ROOT="$(git rev-parse --show-toplevel)"
TV_INDEX="$TV_ROOT/docs/handoff/score-division.json"
TV_PY="${TV_PY:-$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["environment_hint"]["python_executable"])' "$TV_INDEX")}"
TV_EVIDENCE="${TV_EVIDENCE:-$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["external_evidence_root_hint"])' "$TV_INDEX")}"
TV_LAYOUT="${TV_LAYOUT:-$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["external_dependency_layout_hint"])' "$TV_INDEX")}"
test -x "$TV_PY" && test -d "$TV_EVIDENCE" && test -f "$TV_LAYOUT"
TV_CHECKS="$(mktemp -d "${TMPDIR:-/tmp}/trainverify-handoff.XXXXXX")"
printf 'Private outputs: %s\n' "$TV_CHECKS"
```

`TV_LAYOUT` 的配置认证 Lean executable 的 hash 和显式 `LEAN_PATH`。不要用 PATH 中碰巧可用的其他 Lean 版本，也不要对共享缓存执行 Lake build。

## 2. 默认只读核查

首先检查源码没有越过这个验收边界。只允许本次六个交接文件与已接受 commit 不同；其余 tracked 内容和工作树都必须干净。若失败，先看差异，不要 reset/stash，也不要自动将它称为已验收的新版本。

```bash
test -z "$(git -C "$TV_ROOT" status --porcelain)"
git -C "$TV_ROOT" diff --exit-code 05584e60f6216b153175c3f49ea1754a7f64d07a -- . \
  ':!README.md' ':!WORKSTREAMS.md' ':!docs/HANDOFF.md' \
  ':!docs/score-division-runbook.md' ':!docs/handoff/score-division.json' \
  ':!docs/handoff/score-division.sha256'
"$TV_PY" -c 'import hashlib,json,pathlib,sys; root=pathlib.Path(sys.argv[1]); d=json.loads((root/"docs/handoff/score-division.json").read_text()); assert all(hashlib.sha256((root/p).read_bytes()).hexdigest()==v["sha256"] for p,v in d["source_files"].items()); print("accepted adapter/test bytes match")' "$TV_ROOT"
(cd "$TV_EVIDENCE" && sha256sum -c "$TV_ROOT/docs/handoff/score-division.sha256")
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$TV_ROOT:$TV_ROOT/Verdict" \
  "$TV_PY" -m trainverify.artifact_tools verify --config "$TV_LAYOUT" \
  --output "$TV_CHECKS/artifact-integrity.json"
```

这一步不加载 pickle、不做新 capture、不启动 Lean 编译。SHA 清单覆盖本切片的 94 个选定验收文件；layout 另核对外部 source/object/依赖绑定。只读完整性核查不是一次新的证明，也不替代源码审查。若修改了 operator、capture、参数、顺序或声明合同，不能仅凭旧 hashes/旧对象通过来声称新输入已证明。

`artifact_tools verify-kernel` 接受的是一种严格的历史 receipt 格式；不要将新的 `kernel-div/result.json` 直接传给它并假设字段兼容。新结果通过索引里的 source/object/log hashes、显式 layout 与原运行记录核查，接口细节见 [artifact tooling](artifact-tools.md)。

## 3. 轻量接手回归

以下只检查文档/CLI 入口和纯分类 guards，不重跑完整 public predecessor 链，也不把少量通过项称为完整 147 项复跑。

```bash
cd "$TV_ROOT"
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$TV_ROOT:$TV_ROOT/Verdict" \
  "$TV_PY" -m pytest -q -p no:cacheprovider \
  scripts/tests/test_developer_entry_docs.py \
  scripts/tests/test_runtime_frontier_score_div_values.py::test_classifier \
  scripts/tests/test_runtime_frontier_score_div_values.py::test_incomplete_division_cover \
  --basetemp="$TV_CHECKS/pytest-tmp" --junitxml="$TV_CHECKS/pytest.xml"
```

原完整覆盖、退出码与精确 IDs 已保存在 `acceptance-final-reconciliation.json` 和 `acceptance-final-1.*`、`acceptance-final-2.*`。两个批次不能漏项、重叠或把历史部分结果补算为通过。完整 public 测试包含较昂贵的源历史重建；没有源码变化时，交接不要求再跑一遍。

## 4. 只有确实需要时才完整重放

这一节是已存在能力的复现方法，不是当前开发任务。先取得可信 captures、rank code、seed/batch authority、内部依赖和显式 layout；仅有 Git clone 不够。外部 recipe 的路径和 hashes 属于输入，不能猜测凭据或下载未知 pickle。

下面调用受维护的 saved-source CLI，使用新 cache，停在 canonical publication 之前；不会 recapture。必须保持 source clean，且输出目录尚不存在。

```bash
TV_RECIPE="$TV_EVIDENCE/acceptance/recipe.json"
TV_RECIPE_SHA="$("$TV_PY" -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$TV_RECIPE")"
TV_COMMIT="$(git -C "$TV_ROOT" rev-parse HEAD)"
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$TV_ROOT:$TV_ROOT/Verdict" \
  "$TV_PY" -m trainverify.frontier_replay --config "$TV_LAYOUT" \
  --recipe "$TV_RECIPE" --recipe-sha256 "$TV_RECIPE_SHA" \
  --expected-commit "$TV_COMMIT" --out "$TV_CHECKS/replay"
```

recipe 必须先通过第 2 节的独立 SHA 清单校验；这里计算的 SHA 只是传递给 CLI，不是将任意新 recipe 重新认证为可信。预期结果为 5 reads、2 unit facts、6 frontier rows、12 个前驱各调用一次，所有 renderer/public flags 仍 false。

若还需要重新编译：

- 先从原 kernel receipt 读取原命令、完整 queries、源码与 import 绑定，而不是执行证据目录中的固定路径 Python controller。
- 使用 `artifact_tools check-lean` 对新生成的 `FreshScoreDiv.lean` 做有界、单线程检查；明确列出全部 7 个声明，输出到新目录。
- 生成六行 joint 后，要把**这次新编译的 division 对象**加入新的绑定/layout，再检查 joint。不能让路径优先级悄悄选中旧对象充当新编译验证。
- 用 `artifact_contracts` 保留完整 Expr/axiom inventory，并对照原 154 个旧合同。禁止删 shape conjunct、换输出前提、放宽轴或提升 trust policy 来通过。
- 具体已执行的输入/命令在 `acceptance/replay-v2-command.json`、`acceptance/kernel-div/result.json`、`acceptance/kernel-joint/result.json`；旧源码、对象、日志都保持只读。

无需为本次交接重编 world/helpers、重做已成功 actual2、重新跑完整 library 或 canonical capture。`lake build` 的默认 target 是 stub，不是这个切片的验收命令。

## 5. 异常分类与停手条件

- 路径/hash/import 缺失：依赖或迁移问题；保留错误，按显式映射修复环境，不修改数学或旧 pins。
- 只有 stdout/receipt parser 失败、Lean 已 exit 0：保留原对象与日志，按既有工具进行独立 readback；不要为修报告重编已成功模块。
- source、raw scalar/类型、parent/fullref、scope/export、顺序或完整 frontier guard 拒绝：先复现来源差异，不能把它当作无关工具故障忽略。
- 真实 kernel/type/axiom 不匹配：停止声称该候选已验收；保留完整 source/object/command/log，按当前声明处理。

后续 AA(3→2)、softmax 值关系、canonical attachment 和 public 完成属于暂停的开发。接手维护的结束标准是入口清楚、既有结果可核验、边界与依赖准确，而不是继续扩展 frontier。
