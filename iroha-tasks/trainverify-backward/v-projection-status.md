# Original V projection backward DAG: verified local checkpoint

The original dV branch now reaches the V projection's **two** BW_linear outputs. It discovers edges by typed fullref and original writer, not adjacency:

- SM: 77 → 82 → 83 → 88.
- PM: 131 → 132 → 140 → 141 → 142 → 143 → 152; corresponding paths on the other three original ranks are discovered from the same fullref rules.
- PM preserves ReduceScatter, transpose, AllToAll, view and AllGather; interleaved Q/K operations are not mistaken for V edges.

The shared DAG has 28 stage-value definitions and 33 same-final-Store equations. Its five original V linear nodes expose ten output equations. Before linear, the carried value is a V activation cotangent, not parameter dW. A linear second output is tagged parameter gradient only when the authenticated original weight's `is_param() is True`; original saved input/weight identities are retained. These parameter gradients remain the original local shards/contributions, not an asserted fully reconstructed global dW.

## Verification

Parent integration regenerated the exact callers and checked:

- `ActualBWVTransposeRead`: 5 kernel/axiom audits.
- `ActualBWVViewRead`: 5.
- `ActualBWVCollectiveRead`: 8.
- `ActualBWVLinearRead`: 10.
- `ActualBWVProjectionDAG`: 33, including both linear outputs.

All pass with only `propext`, `Classical.choice`, `Quot.sound`. The first collective build correctly reported a missing `SourceAllGatherRead.olean`; the unchanged helper was compiled from current source, then collective caller and DAG were rebuilt successfully. No semantic workaround was used. Recursive local source/object/axiom receipt closure was checked, with external base/data dependencies pinned by `check_kernel.py`.

Parent focused test suite: **28 passed, zero skipped**. Independent source review passed. Its optional shared-output-race finding was resolved: generator tests now use a module-scoped temporary directory and pass `output=` explicitly, including the negative preservation case. Focused rerun: **2 passed, 26 deselected**; narrow independent follow-up review passed. All five generated Lean files in the isolated test directory are byte-identical to the kernel-checked artifacts. Production generator/proof bytes did not change in that test-fixture fix.

Private evidence: `.hermes/backward-kernel/ActualBWV*-kernel.json`, `v-projection-focused.xml`, `v-projection-isolation.xml`, `v-projection-review.json`, `v-projection-isolation-review.json`.

This closes the local original-source V path, not whole-capture success, cross-SM/PM gradient equivalence, or Torch/autograd refinement. The next cross-graph dependency is recorded in `backward-value-blocker.md`; no unsupported saved-primal or cotangent equality is inserted as a premise to claim completion.
