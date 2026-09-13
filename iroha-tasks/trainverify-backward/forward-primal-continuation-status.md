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

## Sequence AllGather -> output-row linear locally closed

Implementation `1eeb8bf436d50e70f2c9a61d313c1724a578f442` is committed in `/home/v-zhouziyu/work/trainverify-backward-forward-q-projection`. It derives Q-like output reconstruction using the existing row-sharded `SourceLinearUnit` theorem, genuine ordered AllGather/linear reads, the predecessor input relation and canonical weight-row bindings. No output relation was added as a premise.

- Fresh original saved-capture render: nine source reads, two new complete DP-unit facts, all eight ordered frontier rows. K/V's four view successors remain explicitly deferred; two residual skips remain retained.
- Q: SM1294 reconstructs PM189/492 for unit0 and PM795/1098 for unit1 on axis2, with local shape `[1,16,32]`.
- Independent original-source census passed. All eleven new read/unit declarations passed exact kernel/axiom checks; unchanged alias/exchange/input-linear modules reused verified objects.
- `ProjectionFrontierJoint.lean` additionally combines **all eight current frontier contracts**, including six Q/K/V DP facts and both skips, under the same successful-run and initial-parameter hypotheses. Kernel passed with only the standard three axioms. This is a conditional shared-context theorem, not a witness that the whole original capture executes successfully.
- Lean rejected reversed weight-row pairing with a producer-equation type mismatch. Synthetic CPU64 checks over both actual source-shaped Q groups also rejected reordered sequence inputs and weight rows; they are not actual model execution or Torch refinement.
- Worker focused suite plus one predecessor regression: **75 passed**. Parent independently reran the public tracer, original-function negatives and missing-partial-descriptor negative: **8 passed, 66 deselected**. Counts overlap and are not additive.
- Independent source-only review passed with no findings. Reviewed source hashes, actual-render source hashes, generated Lean sources and exact kernel objects were checked against the same final source.

## Q output hidden-to-sequence exchange locally closed

Implementation `1de57d456ede689aeb25a4db4742bbe4dc03092a` in `/home/v-zhouziyu/work/trainverify-backward-forward-q-exchange` consumes the original rank-three AllToAll `(idim=2, odim=1)`. Fresh source replay and independent raw identity/metadata/schedule census passed: four reads and two complete value relations, with all eight frontier rows preserved. Q's SM1294 now reconstructs PM198/501 and PM804/1107 on axis1, each local shape `[1,8,64]`. K/V's four facts remain explicitly deferred to their views and both residual skips remain intact.

- All six new declarations and the joint of all eight full frontier contracts passed kernel, standard three axioms only. Unchanged predecessor objects were reused after exact source/import/dependency checks.
- Reversing only the original AA read's peer order was rejected by Lean with source-read and downstream pairing type mismatches. Independent synthetic integer-value CPU checks on both actual source-shaped groups also rejected peer and destination reordering; these are not original model execution.
- Final worker new-suite plus one predecessor regression: **78 passed**. Parent public tracer, nonconsumed descriptor negatives and truthful deferral tests: **13 passed, 64 deselected**. Counts overlap.
- Independent source-only review passed against the final source hashes. One provisional render was rejected by the parent source-stability guard while the worker added truthful unknown-consumer deferral; the later final-source replay passed. No stale provisional result is used for acceptance.

## Original projection views locally closed

Implementation `00350e6de795cb3176339ce982be56da46cbca16` in `/home/v-zhouziyu/work/trainverify-backward-forward-projection-view` is committed and source-clean. Original `torch.Tensor.view` rank-three-to-rank-four reads derive six complete DP-unit output contracts, retaining both residual branches and every frontier row in order.

- Final-source saved-capture replay and independent raw census passed: **15 reads, 6 new complete facts, 8 frontier rows, 2 retained skips**.
- Q view: SM1297 -> PM199/502 and PM805/1108, axis1, local `[1,8,4,16]`.
- K view: SM1299 -> PM207/510 and PM813/1116, axis1, local `[1,8,4,16]`.
- V view: SM1301 -> PM215/518 and PM821/1124, axis2, local `[1,16,2,16]`.
- All **21 new read/unit declarations** and the joint of all eight complete frontier contracts passed kernel with only the standard three axioms. The final inventory-only fix preserved proof bytes, so exact verified objects were reused after final-source replay. The joint remains conditional on the common original runs and initial parameter relations; it is not a whole-capture success witness.
- Final complete view suite: **137 passed**. Parent independently reran **10** signature/parent/public tests and then **8** carry/all-peer tests; these overlap the complete suite and are not additive.
- Early source review found four unfinished fidelity guards (live function, strict rank-four metadata/flags, SM/PM output-parent identity, rank-aware successor edges). Their RED cases were fixed and independently re-reviewed. Later, parent reproduced coherent deletion of both skips plus classifications. The fix now independently expands the original residual fork via normalization/projection ancestry, including authenticated PM exchanges, and checks every original sibling for every DP unit. It uses neither a fixed skip count nor a second predecessor render. Coherent one/all-unit deletion and substitution with a genuine earlier skip are rejected.
- Final carry/source review matches committed implementation and test hashes. Both local-only and ordered all-peer successor metadata have public positive/negative coverage. The same-shaped wrong-projection-input Lean mutation was rejected; exact-index CPU checks passed for all six original source-shaped view groups, with reordered/layout-wrong negatives. CPU values are synthetic, not original model execution.

The next stage is the distinct original rank-four exchanges **(1,2), (1,3), (2,1)** after these views. Their source inventory is retained but their values are not yet closed by this checkpoint. Saved-X1317 remains unproved.

## Public and final-LN boundary

The original forward owner's full sequence-alias bundle was rejected by the 2,500,000-byte limit at 2,504,714 bytes. That owner's separate codec/assembly worktree is untouched. Local kernel-checked incremental modules above are **not** a budget-passing canonical bundle, whole-model/public acceptance, Torch refinement, or a proof of saved-X1317. No upper limit was raised and no theorem contract was shortened.

Private exact sources, raw checks, logs and receipts are under `.hermes/forward-value-continuation/`: `alias/`, `alias-probe/`, `exchange/`, `input-linear/`, review JSONs and the original-input-linear census. `render_local.py` replays source stages and `kernel_local.py` checks incremental modules against the exact accepted forward closure. These are local diagnostics, not replacements for canonical publication gates.
