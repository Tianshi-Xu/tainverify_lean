# Original BW_matmul two-output source reads

## Contract and scope

- Original nnScaler `torch.matmul` mirror / `torch.autograd.grad` backward.
- Ordered source ports `[G, X, Y] -> [dX, dY]`; both X and Y are **saved primal values**.
- `dX = G @ transpose_last_two(Y)`; `dY = transpose_last_two(X) @ G`.
- In attention, the second primal can be V. Its gradient is dV, **not a parameter dW**. No WRED/parameter-gradient claim is made here. Original partial-gradient valmaps remain intact.
- Supported domain: rank >= 2, positive dimensions, identical batch prefixes, matching matrix contraction dimensions, two distinct output ports. Vector promotion and broadcasting fail closed because the current Denote batched kernel has no broadcast/reduction semantics.
- Raw mirror identity, IR tensor metadata, ordered fullrefs/versions, source writers, exported call identity, lowered ports/shapes, original empty kwargs/params, and complete execution order are checked before rendering. Both saved operands and G must survive the selected node and full suffix.

These are **conditional reads in the same final Store** from the original successful `runWithInputs`; they do not establish success of the full captured run, SM/PM gradient equivalence, autograd refinement, or public/whole-model completion. All renderer proof-status flags remain false.

## Exercised original frontier

| World | BW_matmul | Forward mirror | Immediate cotangent producer |
|---|---:|---:|---|
| SM | 77 | 48 | BW_transpose 76 |
| PM rank 0 | 131 | 81 | AllToAllPrim 130 |
| PM rank 1 | 367 | 317 | AllToAllPrim 366 |
| PM rank 2 | 603 | 553 | AllToAllPrim 602 |
| PM rank 3 | 839 | 789 | AllToAllPrim 838 |

No collective is skipped or replaced by an identity. This slice reads its cotangent at the original post-collective fullref; deriving the preceding collective's value is not silently assumed by a cross-store theorem.

## Evidence

- TDD: first original-reader test failed at missing reader; source/helper/witness absence was independently observed as RED. Original CPU/authority checks then passed, followed by the Lean helper and witness.
- Final focused Python suite: **100 passed, 0 skipped** (matmul, linear, view, transpose). Includes original captured shapes, rank3/rank4 rectangular batched float64 autograd against independent scalar-index contractions, coordinated port mutations, both saved versions, metadata/valmap mutations for G/X/Y/dX/dY, cloned mirror identity, source/export/order/suffix mutations, and unsupported domains.
- Kernel: `SourceBWMatmulRead.lean` exports two source-read theorems. `ActualBWMatmulRead.lean` exercises five original nodes / ten caller theorems against the existing exact runtime-world data. `MatmulReadWitness.lean` audits twelve declarations including `caller_nonvacuous`.
- Joint witness: shape `[1,2,2,2]`, G=3..10, X=1..8, Y=11..18. One successful checked run preserves all three inputs and supplies both nonzero/nonconstant derivative tables. It excludes swapped outputs, saved-value substitution, missing transpose, and equalized batches. The same table data are checked independently with Torch and scalar-index sums.
- Kernel projection negative control: reusing the original second-output theorem as a first projection fails with the expected `Type mismatch` (`.2` versus `.1`).
- Axiom policy: only `propext`, `Classical.choice`, `Quot.sound`; no admitted proof or native-decision axiom.

## Reproduction

Use the capture interpreter and explicit tree imports. Existing captures are trusted local inputs; no recapture or shared rank-cell cache writes occur.

```bash
R=/home/v-zhouziyu/work/trainverify-backward-matmul-next
P=/home/v-zhouziyu/.venvs/trainverify-capture/bin/python
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPATH="$R:$R/Verdict"
export TRAINVERIFY_CAPTURE_ROOT=/home/v-zhouziyu/trainverify-audits/general-parallel-internal1
"$P" "$R/iroha-tasks/trainverify-backward/render_actual_matmul.py"
"$P" "$R/iroha-tasks/trainverify-backward/check_kernel.py" "$R/trainverify/denote/SourceBWMatmulRead.lean"
"$P" "$R/iroha-tasks/trainverify-backward/check_kernel.py" "$R/.hermes/backward-kernel/ActualBWMatmulRead.lean"
"$P" "$R/iroha-tasks/trainverify-backward/check_kernel.py" "$R/iroha-tasks/trainverify-backward/MatmulReadWitness.lean"
"$P" -m pytest "$R/scripts/tests/test_runtime_backward_matmul_reads.py" \
  "$R/scripts/tests/test_runtime_backward_linear_reads.py" \
  "$R/scripts/tests/test_runtime_backward_view_reads.py" \
  "$R/scripts/tests/test_runtime_backward_transpose_reads.py" -q
```

Private outputs and source/object/axiom receipts live under `.hermes/backward-kernel/`:
`SourceBWMatmulRead-kernel.json`, `ActualBWMatmulRead-kernel.json`,
`MatmulReadWitness-kernel.json`, `MatmulSwappedNegative-kernel.json`,
`matmul-focused.xml`. Dependency reuse is checked against the existing source/object receipt; changed modules are freshly compiled with Lean v4.32.2. No whole-corpus cold-build claim is made.
