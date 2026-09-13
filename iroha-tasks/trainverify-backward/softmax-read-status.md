# Original matmul → softmax backward checkpoint

Original nodes: SM matmul77 → softmax78 (FW47); PM matmul131/367/603/839 → softmax133/369/605/841 (FW79/315/551/787).

The backward saved operand is the forward **input logits**, not the probabilities. The matmul saved left input is separately joined to that forward softmax's output fullref. The derivative is recomputed as `p * (G - sum(p*G,last))`, with `p = softmax(saved_logits)`; no saved-output shortcut or missing-dot formula is admitted. Raw kwargs restrict softmax to the last axis with no dtype conversion, whereas the existing lowering emits empty params.

Evidence:
- Rolling RED→GREEN from missing reader, unsupported raw-domain/mirror/port/suffix guards, missing consumer module and missing joint witness.
- Integration focused tests: **94 passed** across softmax source/consumer/witness and matmul regressions, no skips. XML `.hermes/backward-kernel/softmax-focused.xml`.
- Fresh kernel: `SourceBWSoftmaxRead` helper; five `ActualBWSoftmaxRead` source reads; five `ActualBWMatmulSoftmax` same-Store compositions; `SoftmaxReadWitness.caller_nonvacuous` and supporting audits. Standard three axioms only.
- Joint witness uses shape `[1,2,1,2]`, logits `[log 2,log 3]` in two rows, cotangents `[1,3]`/`[2,6]`, and exact derivatives `[-12/25,12/25]`/`[-24/25,24/25]`. Nonzero/nonconstant inputs, preserved saved logits, nonzero/nonconstant outputs, row-sum-zero, distinct batches, and no-cotangent/no-saved/no-missing-dot alternatives all inhabit one successful checked run. The same data are checked against CPU float64 autograd.
- Independent source review passed: `.hermes/backward-kernel/softmax-review.json`.

Reproduce with the existing capture interpreter and explicit `PYTHONPATH=ROOT:ROOT/Verdict`, `TRAINVERIFY_CAPTURE_ROOT=/home/v-zhouziyu/trainverify-audits/general-parallel-internal1`. Run `iroha-tasks/trainverify-backward/render_actual_softmax.py`, then `check_kernel.py` for helper, source reads, and composition in dependency order. Prior `ActualBWMatmulRead` is the existing exact producer import. No recapture or shared rank-cell cache writes.

Scope remains conditional original final-Store value reads and local nonvacuity. Full-capture successful execution, forward saved-value SM/PM reconstruction and cross-model gradients are not proved by this checkpoint. Next active slice is original second-output dV → ReduceScatter, preserving its contribution valmaps.
