# Score-division：已验证的源码冷构建交付件

这里发布的是已有 **division + 六行 mixed joint** 的重建输入与验收证据，不是新 frontier，也不接入 canonical 默认生成链。

- 已实际从源码编译 **239 个任务模块 + `ColdContracts`**；未使用旧任务 `.olean`、旧共享包缓存或旧安装工具链。
- **154 个完整 Expr 合同**保持一致，**8,223 项源码公理检查**满足 kernel3。
- 完整 import/source closure 为 **5,151 个模块**。任务源码中 94 个来自固定公开 Git tree、2 个来自固定公开历史；另外 **143 个已接受的生成源码**随本目录发布。它们是复用的原字节，不是重新生成。
- 原冷构建耗时 **80.81 分钟**；最多四个单线程 Lean 编译器。逐模块命令、退出码、源/依赖/对象 hashes 和官方原生依赖来源均已记录。

## 从本仓库重建

要求兼容的 Linux x86-64、Python 3.11+、Git、curl、tar、zstd、`sha256sum` 和 `/usr/bin/time`，以及访问公开 GitHub/官方 Lean、mathlib 缓存的网络。无需旧实验目录、旧 `.olean`、旧共享包缓存、nnScaler、Torch 或 GPU。

**输出必须放进新的私有目录，不要直接在本目录运行构建。**

```bash
set -euo pipefail
TV_ROOT="$(git rev-parse --show-toplevel)"
TV_ARTIFACT="$TV_ROOT/artifacts/score-division-cold-build"
(cd "$TV_ARTIFACT" && sha256sum -c SHA256SUMS)
TV_COLD="$(mktemp -d "${TMPDIR:-/tmp}/trainverify-lean-cold.XXXXXX")"
tar -xzf "$TV_ARTIFACT/portable-rebuild-inputs.tar.gz" -C "$TV_COLD"
python3 "$TV_COLD/restore.py" --build
```

该命令获取源码 pin `97547f38242a61d89b30e1970ec8faf64d82a105` 及两份已列明的历史源码，解包并校验 143 份补充源码；下载校验官方 Lean 4.32.2，按精确 Lake revisions 新建九个 package checkout，再从官方缓存取得依赖对象。随后仅按目标 DAG 编译、核对完整合同和公理，不运行整个旧 goal corpus。

新运行必须同时得到成功的 `build-result.json`、`contract-verification.json`、`all-module-axioms.json`。若只想验证源码获取，把最后命令替换为 `python3 "$TV_COLD/restore.py" --skip-provision`；**这不等于再次冷编译**。不要使用 `python -O` 跳过脚本中的断言，也不要把已有产物/receipts 放进新目录后称作冷构建。

## 文件与来源

- [portable-rebuild-inputs.tar.gz](portable-rebuild-inputs.tar.gz)：完整可运行输入胶囊，保持验收时的原字节。SHA256：`299c1f12b2d1c80180a797bdafbc6af5743a18f83ccc1d63daab9076e49c48b8`。
- [inputs/](inputs/)：胶囊的可读展开版本，便于审查脚本、源码清单和预期合同；其中 [minimal-missing-sources.tar.gz](inputs/minimal-missing-sources.tar.gz) 仅包含 143 个 `.lean` 文件，原始大小 2,638,213 字节、压缩大小 320,194 字节。
- [result.json](result.json)、[REPORT.md](REPORT.md)：原冷构建完成时的冻结结果和报告。
- [evidence.tar.gz](evidence.tar.gz)：原逐模块日志/计时、完整合同、公理结果、完整 import/source closure、工具链和包原生文件 hashes 等文本证据；成员清单见 [evidence-members.json](evidence-members.json)。不含编译对象、工具链二进制、包缓存、capture pickle 或 tensor 文件。
- [publication.json](publication.json)、[SHA256SUMS](SHA256SUMS)：本次仓内发布的范围及文件指纹。

`inputs/` 与胶囊中同名文件逐字相同。冻结结果及证据里的本机绝对路径只是当时的来源/命令记录，**不是恢复时需要创建的依赖路径**。其中 `uploaded: false`、报告里的“等待 publication”等描述的是验收快照时点；当前提交另行发布输入，不重写旧记录来伪造历史。

## 验证边界

本次发布沿用已完成的真实冷编译与 kernel3 检查，并做发布成员/hash 校验和新的胶囊源码恢复检查；不把这些轻量校验称为第二次完整编译。已接受的 `.lean` 源码和构建脚本不作数学或行为修改。官方工具链/包对象将从固定公开来源重新获取，历史对象逐字节相同不是成功标准。

本仓库现在包含该既有 Lean 结果所缺的源码补充。它不意味着新 capture 已被证明，也不授权删除所有其他实验材料；原始 capture/input/Python 恢复、Torch refinement、canonical attachment 和整模型共同执行 witness 保持各自边界。入口说明见 [当前交接](../../docs/HANDOFF.md)和[运行手册](../../docs/score-division-runbook.md)。
