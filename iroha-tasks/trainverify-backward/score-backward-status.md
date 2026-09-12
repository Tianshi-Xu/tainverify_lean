# Original score-gradient DAG checkpoint

The first attention score backward path now composes original matmul→softmax→div→second matmul; PM retains **both** real AllToAll stages. The DAG reuses named Store-dependent values rather than recursively duplicating every ancestor expression.

Exact selected sources:
- SM softmax78 → div79 → matmul80.
- PM softmax133/369/605/841 → AA134/370/606/842 → div135/371/607/843 → AA136/372/608/844 → matmul137/373/609/845.
- Both outputs of the second matmul remain activation gradients with both saved primal fullrefs/values retained. No parameter-dW label is introduced here.

Raw `torch.div` constant `4.0` is authenticated independently of lowered `[4]`. The supported scalar domain is strictly positive integral-valued literals without rounding. Nonintegral floats, booleans, zero/negative/nonfinite scalars and tensor divisors fail closed; no `int(4.5)` approximation. The saved X is still source/shape authenticated, but the true derivative G/c does not depend on its values.

Evidence:
- Rolling RED→GREEN: original div reader/domain/authority negatives; missing score DAG; softmax reader's missing standard ordered output-port interface (added aliases derived from the existing actual output).
- Parent focused tests **114 passed**, zero skips; `.hermes/backward-kernel/score-focused.xml`. Worker independently ran 212 div/softmax/matmul/linear focused regressions before integration.
- Fresh source kernel: five `ActualBWDivRead` callers, eight `ActualBWScoreCollectiveRead` exchange callers, ten `ActualBWScoreMatmulRead` projection callers.
- `ActualBWScoreDAG`: **28 shared value/read nodes**, including **10** second-matmul projection targets and **8** original exchanges, all kernel checked. Standard three axioms only.
- `DivReadWitness.caller_nonvacuous` exhibits nonzero/nonconstant cotangent/saved tensors, preserved inputs, exact G/4 values, and rejects identity/saved/multiplication alternatives in one successful checked run.
- Independent static review: `.hermes/backward-kernel/score-review.json`.

Reproduce with the capture interpreter and tree-local PYTHONPATH using `iroha-tasks/trainverify-backward/render_actual_score_backward.py`. Build the three emitted source modules in parallel after their helpers, then build `ActualBWScoreDAG` after all three. It imports the existing exact `ActualBWMatmulSoftmax` root; original runtime-world TIDs/fullrefs/shapes/execution order are joined to its receipt before rendering. No recapture, source model mutation or shared rank-cell cache write.

This is conditional same-final-Store composition. It does not derive the cross-graph attention cotangent or saved-Q/K/V/logit/probability relations from initial conditions. Actual cross-SM/PM closure remains dependent on accepted forward value authority, not on shapes or older same-shaped layer facts.
