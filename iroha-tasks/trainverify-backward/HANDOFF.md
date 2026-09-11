# Backward / DP work line

## Ownership and baseline
- Owner: Methode, Discord backward thread; independent branch `trainverify-backward`.
- Worktree: `/home/v-zhouziyu/work/trainverify-backward`.
- Immutable base: `b1b2fb45a521488f9b7b517982e11fabaaaf0d10` (clean when created).
- Forward tree is read-only: `/home/v-zhouziyu/work/trainverify-dp-prefix-cost-closure`.
- Own this document and new backward-specific authority/read helper/tests only. No canonical renderer/scanner/import/public entry edits; exact module contracts and commits will be handed to forward integration.

## Existing evidence and reuse
- `Verdict/runtime_prefix.py` already supports BW_linear, with ordered `[dy,x,w]`, two outputs and rank2/rank3 shape checks. Existing dX/dW theorem families are under audit, not to be reimplemented blindly.
- `denote/SourceValueRead.lean` supplies original successful run / SAME-final-Store source reads; `SourceLinearRead.lean` is the forward pattern.
- Forward local acceptance: audit `dp-prefix-cost-closure/output-projection/STATUS.md` records output projection source commit `d9f53deb49f839d731a031c64c1e08ad27f464a6`. This is historical evidence, not a new build in this worktree.
- Existing real captures to reuse, without recapture: `trainverify-audits/general-parallel-internal1/global-b2/capture.pkl` and `p2-r4/capture.pkl`.

## First slice / open obligations
Audit original FW/BW pairing, saved x/w identity/version and cotangent before adding source read certificates. Distinguish source authority from exported DTO and renderer. No assumptions about loss/seed/DP scaling; no output equality premises.

Input reconstruction from the forward chain, seed provenance, branch accumulation and DP/WRED remain explicit upstream obligations until actually discharged. Local conditional read theorem is not a whole-model result.

## Source boundary checkpoint (Python-only)
- Own: `trainverify/backward_linear_authority.py`, `scripts/tests/test_backward_linear_authority.py`, this document and `inspect_capture.py`.
- `bind(cells, source_index)` consumes actual transient `IRBpOperation` / `.mirror`, complete original ordered IR metadata and source fullrefs. It records the independent cotangent/saved-X/saved-W roles, dX/dW outputs and contraction convention; it rejects changed saved versions/owners, reordered outputs, mismatched derivative identities and exact-fullref suffix overwrite.
- Raw caller cells must come from the existing source loader. Binding this record to writer/export/call authority, lowered graph execution order and the shared proof DAG remains the next interface step. This record is not itself an authenticated whole-model certificate.
- Actual captures: first BW is SM cid62 / FW cid57 and PM rank0 cid348 / FW cid345. Source formulas: `Denote.lean:381` rank2/rank3 backward agrees with local `torch.nn.functional.linear` derivative over supplied cotangent; no added local scaling. PM first dX has value-part `(0,2)` (partial sum, not a numerical division by two). Original runtime seed/normalization remains an external obligation.
- Executed strict RED→GREEN: missing binder → positive; six fullref/order failures → guard → green; five newly exposed mirror/metadata/version/suffix failures → guard → green. `saved-ir` is rejected by the prior saved-fullref guard, not counted as new metadata-guard coverage.
- Test fixture clones all Cell slots explicitly: ordinary `copy.copy(Cell)` drops transient IR authority through `__getstate__`; clone acceptance is checked before mutations.
- Focused command (13 passed, 0 skipped):
  `TRAINVERIFY_CAPTURE_ROOT=/home/v-zhouziyu/trainverify-audits/general-parallel-internal1 PYTHONPATH=/home/v-zhouziyu/work/trainverify-backward:/home/v-zhouziyu/work/trainverify-backward/Verdict /home/v-zhouziyu/.venvs/trainverify-capture/bin/python -m pytest /home/v-zhouziyu/work/trainverify-backward/scripts/tests/test_backward_linear_authority.py -q --tb=short`
- Source-only inspection: same PYTHONPATH/Python, run `/home/v-zhouziyu/work/trainverify-backward/iroha-tasks/trainverify-backward/inspect_capture.py`; uses `_prepare_rank_cells` in memory, never build_graph rank-cell cache.

## Source-read checkpoint (kernel accepted, not whole-model)
- First Python-only checkpoint: `0e55e22d7ae83a5e29c8627a9e7af6e3fef9c240`.
- Own additionally: `Verdict/runtime_backward_linear_reads.py`, `trainverify/denote/SourceBWLinearRead.lean`, `scripts/tests/test_runtime_backward_linear_reads.py`, files under this handoff directory, and the one scoped `.gitignore` entry for local kernel output.
- `render_read(view, cells, snapshot, source_index, order, label)` binds original BW+FW writer/export/call and ordered fullrefs to the lowered source graph, revalidates execution order, rejects nonempty params and checks the complete selected-node/execution suffix. It returns two named dX/dW theorem fragments plus explicit source/caller obligations. It never edits or publishes the canonical entry.
- Caller contract: import `denote.SourceBWLinearRead` and retain the existing `*Graph`, `*Scope`, `*Peers`, `*InputRequests`, `*Node_i`, `*DenoteWithInputs` definitions. Each theorem takes only the original successful run and concludes the corresponding final-Store `bw_linear` projection. Seeded runs may instantiate the initial Store with the authenticated existing seeded initializer; no gradient value is assumed.
- Actual first SM + all four PM ranks: source/execution indices `(64,64), (109,217), (345,219), (581,639), (817,641)`. Complete original tensor inventory, injective lowering IDs, shapes and execution order match the accepted canonical data before rendering.
- Final focused gate: **72 tests + 443 subtests passed**, zero failures/skips. Includes new call/export/port mutations, source params RED→GREEN, invalid initial cotangent RED→GREEN, and independent node-vs-IR CID/name RED→GREEN. Existing seeded-prefix and scheduling regression suites are included.
- Serial Lean v4.32.2: 2 generic read declarations, 7 witness declarations, 10 actual graph declarations passed; each exact axiom set is only `propext`, `Classical.choice`, `Quot.sound`. Nonzero caller witness uses dy `[2,3,5]`, x `[2,3,7]`, w `[5,7]`; aliased outputs are rejected by InputSchedule. `ACCEPTANCE.json` records exact bytes/objects and real exit codes.
- Kernel setup used verified source/object dependencies in a private per-module overlay. Importing the whole canonical RuntimeWorld initially exposed unused missing helper caches; the correct minimal dependency is its unchanged `TrainVerifyRuntimeWorldData`, avoiding unrelated forward proofs. No shared cache writes or parallel Lean processes.
- Reproduce actual source fragment using the documented capture env/PYTHONPATH and `iroha-tasks/trainverify-backward/render_actual.py`; then run `python /home/v-zhouziyu/work/trainverify-backward/iroha-tasks/trainverify-backward/check_kernel.py <absolute .lean path>` serially for the helper, LeanWitness, and `.hermes/backward-kernel/ActualBWLinearRead.lean`. Standalone scripts use absolute resolved roots. Existing captures and accepted dependency receipts are required, not fabricated.

## Independent review follow-up
- Review of exact `9864fd52` independently reproduced two rejected-at-no-boundary defects: a raw mirror function signature different from `torch.nn.functional.linear`, and a changed paired FW opcode in the lowered graph, both previously yielded unchanged read fragments. Parent reproduced both with failing regression tests before patching.
- The binder now checks the actual original forward function signature; the renderer joins opcode/kwargs/params/fullrefs/shapes/scope for **both** FW and BW. This does not change any theorem statement or operator semantics.
- Final targeted Python gate: **26 passed**. In-memory deletion of each new guard independently causes its named regression to fail with `DID NOT RAISE ValueError`; restored tests pass. Fresh actual rerender is byte-identical to the already kernel-checked 8,480-byte fragment, so no unrelated Lean recompilation was needed.
- The external review session ended on a provider error before a final verdict; no independent final PASS is claimed. Findings above were separately reproduced and closed by the parent.

## Seed / BW_sum checkpoint
- Linear source consistency follow-up committed as `d10d8016d44ea926778ed0e5b47d51350a78d07e`.
- New owned modules: `Verdict/runtime_backward_seed_reads.py`, `trainverify/denote/SourceBWSumRead.lean`, `scripts/tests/test_runtime_backward_seed_reads.py`; diagnostic caller, actual generated fragment and reproducible seed runner are in this directory.
- Public `render(worlds, config, handoff_root)` calls existing `runtime_seed_feed.load_bundle` afresh. Actual complete source captures, existing run/event/PT inventories, input reference and current-run parameter values were validated. The observed unit seeds are not a default normalization decision. The generic sum theorem supports arbitrary supplied seeds; witness seed=3 proves every output value is 3 with shape `[2,3,5]`, no division by tensor size.
- The new fragment derives original BW_sum reads, final seed preservation via the existing original-run frame theorem, then broadcast tensor values from the existing authenticated seeded initializer. Fullrefs/mirror metadata/function identity, writer/export/call, params and complete execution suffix are retained. It does not alter the seed adapter or canonical entry.
- Final focused gate: **36 tests + 40 subtests passed**. New seed-ref RED→GREEN plus positive source/runtime authentication. Four in-memory guard removals (seed ref, seed value contract, original function, params) each fail the exact regression with `DID NOT RAISE`; restored tests pass. The suffix negative is rejected by the inherited full scheduler guard and is not counted as coverage of the later local suffix check.
- Serial Lean: **1 generic + 10 witness + 15 actual declarations**, all kernel accepted with only the kernel triple. `ACCEPTANCE.json.seed_checkpoint` records exact sources, outputs and real exit codes. Only unchanged Data + seed Prefix0000/Support and existing frame dependencies were reused; no whole-model rebuild or capture-cache mutation.
- Reproduce actual seed fragment: same capture env/PYTHONPATH/Python, run `iroha-tasks/trainverify-backward/render_actual_seeds.py`, then serial checker on `SourceBWSumRead.lean`, `SumWitness.lean`, `.hermes/backward-kernel/ActualBWSeedRead.lean`.

## Backward AllToAll / cotangent checkpoint
- Seed/BW_sum checkpoint committed as `4b505bd26ae73a56b997711c11e074c0555cb0db`.
- New owned module `Verdict/runtime_backward_cotangent_reads.py` freshly loads the existing source collective snapshot, requires the actual `backward_context.status == structurally-bound`, and joins exact ordered peer gradients to the already authenticated BW_sum certificates and the original BW_linear input.
- Real backward nodes retain raw FW-looking kwargs `[idim=2,odim=1]`; independently bound runtime/autograd scope proves their effective parameters are `[1,2]`. Source indices 108/344/580/816 feed the four original linear cotangents. No group sorting, dropped contributions or across-DP pairing is introduced.
- The new shared-DAG fragment reuses prior seed and linear theorem names. Its conclusions expose each faithful sender-split/receiver-gather cotangent expression and substitute it separately into dX and dW. It does **not** yet prove that the corresponding DP/TP reconstructed gradients equal the SM gradient.
- Exact actual fragment: **16 kernel declarations**, all kernel triple. Final **27 focused tests + 12 subtests passed**. Effective-dimension, peer-order, and gradient-version guard deletions each trigger their named regression. Missing/duplicate contributions are rejected after the fresh seed predecessor was accepted.
- Inherited faithful-scope heldouts include noncontiguous K=3 groups. Replayed **24 CPU source-flow cases for K=1,2,3** using asymmetric position/rank values; K3 output explicitly retained rank order. This is a derived source-flow CPU check, not distributed Torch execution; the new capture-to-DAG slice was actually exercised on TP2/DP2 only.
- Reproduce with `render_actual_cotangents.py` followed by the serial checker on `.hermes/backward-kernel/ActualBWCotangentRead.lean`; it imports the already checked actual seed and linear fragments instead of regenerating another proof architecture.

## Next real blocker / integration status
- Seed → BW_sum → faithful reverse AllToAll → original dX/dW expressions are locally connected under the original successful seeded run.
- Distributed gradient equality still needs **final LayerNorm saved-X reconstruction**, **initial weight frame/layout**, and source-derived shape relations. Forward saved-X value reconstruction remains an explicit interface obligation of the forward line; dW cannot discard it just because dX uses only X's shape.
- Next backward-owned scope is the original dW contribution → DP WRED mapping/scaling, while checking which existing shape/parameter facts can close dX without waiting for full forward values.
- All emitted proof/kernel/public/Torch flags remain false; external exact-byte receipts certify these local kernel declarations only. Canonical/main integration not done; no push, publication or cron.
