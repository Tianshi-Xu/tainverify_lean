# Forward saved-primal continuation: local kernel checkpoint

This advances the dependency described in `backward-value-blocker.md`; it does not claim that final-LN saved input 1317 is reconstructed yet.

## Original 1293 -> aliases -> K/V exchange

- Reused immutable sequence-alias source snapshot `0c97112545fa9e3f73dda34edf88e07ef06dc550`, not the worker repair alone.
- Fresh real saved-capture replay rebuilt original graph/lineage/parameter authority. Public stage calls received the same six original objects, not a saved frontier receipt. Capture caches and all new proof outputs were private; no new model capture or shared-cache writes.
- Alias stage: five original reads, six complete DP-unit facts, eight frontier rows with two retained skips. All eleven declarations passed the local kernel/axiom gate on an exact accepted predecessor object closure. Fresh replay bytes matched the prior diagnostic bytes that were kernel-checked.
- New selective projection-input exchange commit: `150b33c9` in `/home/v-zhouziyu/work/trainverify-backward-forward-exchange` (clean after commit). It reuses the existing selective AA mechanics while preserving their default text and complete receipt exactly. It independently validates complete original alias input/output descriptors, all ordered slots, and coherent SM/PM original parent identities, including deferred branches.
- Fresh actual AA stage: eight original reads, four new complete value-reconstruction facts. All eight frontier rows remain in order: K/V advance, two Q AllGather branches remain explicitly deferred, and two residual skips are retained.
- All twelve AA declarations and a joint theorem containing all four complete shape/local-shape/value contracts passed kernel, using only `propext`, `Classical.choice`, `Quot.sound`.
- Independent raw-census checks passed for both stages. A wrong saved-input 1317 substitution and a wrong exchange reconstruction axis each failed Lean as expected; neither was an import/cache failure.

Final new renderer suite: **110 passed**. Combined new/old regression run: **152 passed** (started before the final coherent-parent guard; the final 110-test run covers that guard). The existing sequence-hidden default full text and receipt are byte-identical to immutable `0c971125`. Independent source-only review passed against the final three source hashes; actual-render start/end hashes match that reviewed source.

## Input-column linear -> ReduceScatter locally closed

`SourceLinearInputUnit.lean` was proved at `6a814f6b` and integrated as `6369141c` in `/home/v-zhouziyu/work/trainverify-backward-forward-linear`. Its arbitrary-D/TP theorem derives global shape, every local partial-output shape, and DP-chunk equality to their ordered sum, from authentic input-feature/weight-column reconstruction and paired local linear reads. Parent recompiled the exact source and a named full-contract probe; kernel3 only. Independent source review passed. The helper alone is a mathematical component; the actual source-bound closure below consumes it.

The existing `SourceReduceScatterRead.lean` was imported unchanged from the backward checkpoint as `1497564d`, with identical SourceValueRead dependency bytes, and recompiled against the accepted forward helper namespace.

An independent original-capture census found an important asymmetry: K uses ReduceScatter dim=1 (sequence), V uses dim=2 (hidden). Both consume genuine partial linear contributions with value part `(local_index, TP)`. The source-bound renderer now derives these axes from source and preserves weight-column pairing, ordered sum and every Q/skip branch. Implementation `c1e06808` plus parent-reviewed function-identity fix `0f877c2e` are committed in the isolated linear worktree.

Final local acceptance:
- Eighteen original reads and four complete cross-SM/PM output facts passed kernel (22 declarations), plus their joint full-contract theorem, kernel3 only.
- K: SM1295 reconstructs PM206/509 on axis1 in DP unit0 and PM812/1115 in unit1; local shape `[1,8,64]`.
- V: SM1296 reconstructs PM214/517 on axis2 in unit0 and PM820/1123 in unit1; local shape `[1,16,32]`.
- All eight frontier rows remain ordered; Q is explicitly deferred and the two residual skips are retained.
- Final **64 tests passed, zero skipped**. Independent source-only review passed against the same final file hashes.
- Parent reproduced four SM/PM wrong-function/missing-IR mutations that passed the old opcode-only checks. The new guard checks the actual original `torch.nn.functional.linear` signature; fixtures now carry that supported signature instead of a synthetic opcode tag. This was our validator's fidelity gap, not an observed nnScaler numerical bug.
- A final real saved-capture replay after that fix passed, including independent raw source/fullref/shape/parameter/axis/ordered-frontier checks. All generated Lean bytes matched their existing checked source/object/import closure, so the final gate reused those exact objects rather than recompiling unaffected modules.
- Independent CPU64 scalar-oracle checks over all four actual source-shaped K/V groups passed with synthetic nondegenerate values and rejected averaging, mismatched weight-column pairing, and the wrong RS axis. They are not real model execution or Torch refinement. A Lean wrong-weight-pair mutation also failed with the expected producer-equation type mismatch.

The next active slice is the deferred sequence-AllGather -> output-row-sharded linear branch (Q-like), in isolated `/home/v-zhouziyu/work/trainverify-backward-forward-q-projection` based on `0f877c2e`. Its current source-shaped census confirms rank0 AG55 -> linear56, but no Q output value theorem is claimed yet. This stage must preserve the already-closed K/V facts and residual skips, and use the row-sharded weight theorem rather than the input-column sum theorem.

## Public and final-LN boundary

The original forward owner's full sequence-alias bundle was rejected by the 2,500,000-byte limit at 2,504,714 bytes. That owner's separate codec/assembly worktree is untouched. Local kernel-checked incremental modules above are **not** a budget-passing canonical bundle, whole-model/public acceptance, Torch refinement, or a proof of saved-X1317. No upper limit was raised and no theorem contract was shortened.

Private exact sources, raw checks, logs and receipts are under `.hermes/forward-value-continuation/`: `alias/`, `alias-probe/`, `exchange/`, `input-linear/`, review JSONs and the original-input-linear census. `render_local.py` replays source stages and `kernel_local.py` checks incremental modules against the exact accepted forward closure. These are local diagnostics, not replacements for canonical publication gates.
