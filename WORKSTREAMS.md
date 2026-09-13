# Shared TrainVerify workstreams

## Shared integration checkout

- Checkout: `/home/v-zhouziyu/work/trainverify-integrated`
- Branch: `integration/trainverify-forward-backward`
- Local integration only; no push or merge to `main` is authorized by this checkpoint.
- Historical worker directories are evidence/development snapshots, not separate canonical implementations.

## Imported handoff boundary

The integration includes the complete committed histories, not selected tip-file copies:

| Partition | Frozen source tip | Scope |
| --- | --- | --- |
| Forward baseline | `3cba09a9355ac509b422a6dfdb7ceeadde66f4c8` | Sequence alias, strict AllGather consumer metadata, v4 fixed-budget representation |
| Forward dependencies built by backward line | `68ab04c0ff2c736a660c09b779488f78f5556aeb` | K/V input exchange + linear/RS; Q gather/linear + exchange; projection views, head exchanges, transpose(1,2) |
| Backward line | `35953c47740ed3a03729f9658b780f5eefe06dea` | Source-bound backward readers/consumers, local proof helpers/witnesses and handoff records |
| Post-transpose continuation | `8db687e1a20d5106be18087f423ceb41d13415fc` | K transpose23, V AllGather replica facts, source-derived retained full-fact binding; includes `cf53bd9a` |
| K middle exchange continuation | `8d916fc0f4455ccd0e187a3d3755ae579978ba6b` | Original K AA(2,1), complete mixed frontier/history binding, unchanged Q/V/carry facts |
| Q/K score matmul continuation | `2f23e3228f8e2f0f00123dafb2cb82c50a2a0c68` | First original ordered Q/K matmul per DP unit; complete score facts, V replicas and residual carries; downstream division/AA inventoried only |

The QKV partition's 21 changed paths and backward partition's 179 changed paths were compared to their exact committed blobs at the merge candidate. All matched. The partitions overlap; these counts are not additive feature counts.

## Single-owner division

- **Integration/parallel line:** shared authority interfaces, canonical frontier/DAG assembly, source budget and whole-model/public acceptance. It reuses the source-bound forward dependency implementations already supplied by the backward line; it does not start another Q/K/V implementation.
- **Backward/saved-primal line:** continuation required for saved primal reconstruction and gradients. The post-transpose continuation has been handed off through merge `b60e7288`; subsequent saved-primal and gradient work remains with this line.
- Before new implementation fan-out, compare related live worktrees and semantic targets (fullrefs, shapes, axes, parameter binding and frontier order). A backward saved-primal dependency can be the same forward task, despite different channel/branch names.
- Shared file edits have one writer. New workers branch from an agreed integrated commit in isolated worktrees and use private caches. Existing active workers are not forcibly rebased, reset or cleaned.
- This file records the intended coordination boundary. It does not claim another chat has received or acknowledged a reassignment.

## Protected unfinished work and evidence

- The historical post-transpose development checkout was retired in the cleanup below. Its complete committed chain remains in the integrated history and under `archive/cleanup-20260913T144750Z/trainverify-backward-forward-post-transpose`.
- `/home/v-zhouziyu/work/trainverify-backward-matmul-next/.hermes/`: private generated source, raw-census, kernel and review receipts; retained at their original paths.
- Only the dependency/evidence roots listed in the cleanup manifest remain materialized. Historical paths in earlier checkpoints describe those runs, not a promise that every old worker directory still exists.
- The original three empty Copilot worktrees were removed in the earlier consolidation. The later complete cleanup is recorded below; recover retired sources through their archive references, not by inventing replacements.

## Acceptance boundaries

- The old backward handoff's statement about the sequence-alias bundle exceeding 2,500,000 bytes describes its earlier checkpoint. The forward baseline already resolved that issue with v4; do not repeat the codec work.
- The accepted **alias-stage** bundle was 2,489,883 bytes. That is not a byte-size result for a newly assembled QKV/backward bundle.
- Source consolidation, Python/public-entry regression and focused helper kernel checks do not by themselves establish canonical whole-model assembly, a successful whole-capture run, saved-X1317 reconstruction or Torch refinement.
- QKV helper/frontier facts remain complete conditional contracts with their original common-run and initial-parameter hypotheses. No premise or theorem was weakened by this merge.
- The post-transpose stage, including the retained-fact fix, and K middle exchange are now inside the canonical attachment boundary (see their checkpoints below). Neither checkpoint implies whole-model acceptance. The integration line owns canonical assembly/acceptance; the backward owner owns saved-primal continuation. Coordinate interface changes before overlapping work.
- At the user's request, no new implementation fan-out starts until this committed handoff and integration verification are complete and the integration worktree is clean.

## Post-transpose handoff verification

- Source handoff: `cf53bd9a` plus `8db687e1`, merged by `b60e7288`. Exact two-file blobs match the source-reviewed fix.
- Integrated regression: **219 passed, zero failures/errors/skips**; complete collected node IDs were partitioned into three disjoint 73-case batches, with persisted JUnit and result reconciliation.
- Fresh integrated saved-source replay and raw census: **9 reads, 4 complete unit relations, 8 frontier rows, 2 deferred Q rows, 2 residual carries**.
- Exact source/object/dependency closure and all-eight mixed-layout joint passed; V retains every-replica equality rather than a fabricated gather-axis contract. All 13 new declarations use only the standard three axioms. This remains local conditional proof evidence, not canonical whole-model acceptance.
- Private evidence: `/home/v-zhouziyu/work/trainverify-backward-matmul-next/.hermes/forward-value-continuation/post-transpose-integrated/` and sibling `post-transpose-integrated-tests/`.
- Both old worker source and shared integration must be clean before subsequent isolated implementation starts. Shared canonical/DAG files remain exclusively owned by the parallel line.

## Canonical projection checkpoint

- Candidate `7c2b0c07f92426cd4a89b2bf570a6677d95820d4` merged locally by `b59140c9b20f4aa57787183c0e86e0558818aa79`; merged code tree `7961f55d21178522ec17fd017a0e4ddc9d46d6d0` exactly matches the independently reviewed preview.
- Canonical attachment now includes all seven source-bound projection stages after sequence aliases, through projection transpose(1,2). The already-imported subsequent post-transpose renderer is preserved but is not yet attached by this checkpoint.
- Fresh saved-capture canonical bundle: **2,486,692 bytes**, all 131 modules within the unchanged strict `<2,500,000` gate. V5 is exact identifier encoding in sealed prefix chunks; the extensible entry keeps its established encoding policy. No mathematical contract or branch was removed.
- All 131 exact-source kernel modules passed (128 fresh, 3 exact reuses), with full object/import/axiom binding to the actual published sources. Standard kernel3 only.
- Reference/candidate comparison: **517 full Lean Expr contracts** (515 public, 2 private) identical; **479 joint declarations**, all 8 stages / 64 frontier occurrences / 16 retained-skip occurrences checked. These remain conditional contracts, not a proof of a successful whole-capture execution.
- Default path: all 31 modules and receipt byte-identical. Focused source suite: 393 passed including real Lean codec controls. Independent final review: scoped PASS, 263 checks; parent reran it, then 35 merge-related tests and the actual bundle admission/readback with merged source passed.
- Evidence: `/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/canonical-projection-frontier/`. Original failed budget run and postprocessing diagnostics are retained; successful kernel/capture work was not rerun to repair bookkeeping.
- Next canonical attachment may consume the handed-off post-transpose stage, including genuine per-DP replica value contracts. Do not use a dummy gather axis for replicas. Saved-primal and later operator development remain with the backward line; no duplicate implementation is needed.
- This checkpoint does not assert whole-model/public completion, saved-X1317 reconstruction, or Torch/CUDA refinement. No push to main.

## K middle-exchange saved-primal checkpoint

- Source handoff `8d916fc0f4455ccd0e187a3d3755ae579978ba6b` is joined by merge `a25ce8081dec89d784188acbaaf51e95981cbaa6`. The two renderer/test blobs match the independently reviewed worker exactly; no canonical attachment or mathematical helper was changed.
- The user authorized the saved-primal line to complete this continuation's real-source, raw, kernel, joint and source-review gates, integrate it, then proceed to the next narrow source frontier. Shared canonical/DAG attachment remains a separate active workstream; do not duplicate or overwrite it.
- Both isolated-worker and integration-candidate saved-source replays passed with private caches and no recapture: **4 new PM reads, 2 complete K unit facts, 8 ordered frontier rows**. The source-derived AA(2,1) output has local shape `[1,2,16,16]` and axis-1 reconstruction; Q remains deferred, V keeps per-DP replica equality with `gather_axis=None`, and both residual carries survive.
- All 6 new declarations passed the Lean kernel with only `propext`, `Classical.choice`, and `Quot.sound`. All 8 complete mixed-layout contracts passed together under the same full-run and `InitialParameterValues` context. Exact accepted predecessor source/object/import closure was checked, including the middle helper's 39-source closure.
- Integrated regression: **125 passed, zero failures/errors/skips** (124 new cases plus the previous public tracer), with complete collected IDs, disjoint batches, JUnit, exit receipts and unchanged source hashes. All 10 freshly emitted fragments, the full frontier details, execution order, bound inputs and fullrefs match the worker replay exactly.
- Evidence: `/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/backward-middle-exchange-acceptance/`, with worker Python/TDD evidence in sibling `backward-middle-exchange-worker/`.
- These are conditional source-value results, not canonical whole-model completion, successful whole-capture execution, saved-X1317 reconstruction or Torch refinement. Renderer flags remain uncompiled/false. The next saved-primal target is the original ordered Q/K score matmul; its downstream SM division and PM AA(1,3) are not yet consumed.

## Canonical post-transpose checkpoint

- Candidate `584f6a2af9f3d13d3ce842ba4d5667f8e11e77a6` is merged by `ba5389e0ba7c0bfb9433d9e9e6b47656bfcbed7f`; actual merged tree `392e35346a84f039aea3eb8fc2203d974b790498` exactly matches the independently reviewed preview against shared head `d925b6f2`.
- Canonical attachment now consumes post-transpose: 9 original reads, 4 new complete unit relations, all 8 ordered frontier rows, 2 deferred Q rows and 2 residual carries. V uses every-replica equality to its DP chunk, never a dummy gather axis or an output-value premise.
- Actual2: **2,494,634 bytes**, all 131 modules inside the unchanged strict `<2,500,000` budget. The 130 non-entry source/metadata records and exact checked objects remain unchanged; the new entry passed the kernel with all 528 public axiom targets, kernel3 only.
- Candidate/reference: **530 full Lean.Expr contracts** identical (including 2 private); all 517 previous contracts retained. **496 joint declarations** checked, retaining all 479 old joints and the complete mixed frontier under the original shared run/parameter hypotheses.
- Independent final scoped review PASS. Parent revalidated its evidence and exact preview identity, then ran the same 30 entry cases on merged code, 13 mixed-contract cases, actual bundle admission/readback and 6 zero-write publication attacks. The first parent wrapper mistakenly expected all 30 cases in the 19-case new entry file; the remaining 11 prior-entry cases were run separately and exact node IDs reconciled, without rerunning the completed 19.
- Actual1's exit139 remains unexplained; successful actual2 does not identify or claim to fix that historical cause. No accepted capture or old kernel module was rerun for this merge.
- At this earlier checkpoint, K middle-exchange source/tests were byte-preserved but not yet canonically attached; the next checkpoint below closes that attachment. Q/K matmul and later saved-primal operator development remain with the backward line.
- Evidence: `/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/canonical-post-transpose/`, especially `final-review/review.json` and `postmerge/gate.json`. This is conditional canonical frontier acceptance, not whole-model/public completion, saved-X1317 reconstruction or Torch refinement. No push to main.

## Canonical middle-exchange checkpoint

- Candidate `63a402beb191604a7b8f2e9d2c3427152a66a249` is merged locally by `6338fe60b8a1a4de569cc1f43cbf48d031d4cd63`. Actual merged tree `789438fdbb0e161d05249e4d2435d6463b820da3` exactly matches the independently reviewed preview against `f01fa062`.
- Canonical attachment now includes the handed-off K AA(2,1): 4 original PM reads, 2 new complete K unit facts, all 8 ordered frontier rows. Q remains deferred, V retains every-replica DP-chunk equality with no dummy gather axis, and both complete residual carry facts/history survive.
- Actual1: **2,498,688 bytes**, 131 modules under the unchanged strict `<2,500,000` cap (1,312 bytes remaining). All 130 non-entry sources/metadata and checked predecessor objects remain unchanged; only the new entry was compiled, with 534 public axiom targets and kernel3 only. No completed capture or entry was rerun for merge.
- Reference/candidate: **536 full Lean.Expr contracts** exactly equal, retaining all 530 prior contracts; **506 joint full Expr contracts** exactly equal, with all 496 previous joint declarations preserved. The real candidate Contracts/Joint checks passed with exact source/object/log/import binding.
- Independent final **SCOPED PASS**, no scope pending: 14,877 checks, 22 rejecting negative controls, 2,644 bound files. Parent read back every bound file and verified the exact staged merge tree, then actual bundle admission/readback, all complete contract bindings and 6 zero-write publication negatives passed on the merged source. The accepted 47-case focused suite is inherited on identical code; 14 inexpensive merged attachment cases were freshly checked (overlapping counts, not additive).
- B1 was an external audit-controller package-root selection defect, not a mathematical counterexample. Frozen `contracts-v2` resolves exactly like Lean, rejects partial namespace shadowing after the complete copy plan, and binds the explicit six-tool transition. Original successful reference source/object/log/command/exit evidence was reused without recompilation; original failed diagnostics remain retained.
- Evidence: `/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/canonical-middle-exchange/`, especially `final-review/review.json`, `contracts-v2/actual1-audit/candidate/complete.json`, and `postmerge/gate.json`.
- This is conditional canonical frontier acceptance, not whole-model/public completion, successful whole-capture execution, saved-X1317 reconstruction or Torch refinement. Q/K score matmul and later operator development remain with the saved-primal line; further canonical attachment requires its explicit source/verification handoff. No push to main.

## Q/K score-matmul saved-primal checkpoint

- Reviewed worker `2f23e3228f8e2f0f00123dafb2cb82c50a2a0c68` is joined by local merge `764faa42b4949855bfc8f749d0e0811552c40ab3`. Shared integration was fast-forwarded to the already-tested merge; code tree `9f041f12b3f565a34edb4246f3c709122e9f907f` matches the isolated integration candidate exactly. Only the two new renderer/test files enter this code merge; this ledger update is separate.
- Fresh saved-source replay on the merge candidate, with a private cache and **no recapture**, emits **5 original reads, 2 complete score unit facts and 6 ordered frontier rows**. The original ordered Q/K matmul produces lowered SM1304; each DP unit has global shape `[2,4,16,16]`, local shape `[1,2,16,16]` and axis-1 reconstruction. V's complete every-replica DP-chunk facts and both residual carries survive; V is explicitly deferred pending its missing original other operand.
- All **7 new declarations** passed the exact-source Lean kernel with only `propext`, `Classical.choice` and `Quot.sound`. All **6 mixed frontier contracts** passed together under the same full SM/PM runs and `InitialParameterValues`; both shape conjuncts remain. The 10 predecessor fragments and full middle-stage detail are byte/typed-wire identical to accepted sources, with exact accepted world, helper, object and transitive import binding. No predecessor proof or mathematical helper was changed.
- Parent independently re-read the worker's complete **200-case** closure (199 new cases plus one prior public tracer), JUnit, exact collected IDs and 390 source pins. **28 fresh integration regressions** passed on the merge candidate; these overlap prior tests and must not be added as independent coverage. Independent source review **PASS**, no findings: 47 bounded probe records, an isolated four-case actual-backend suffix control, and a non-square all-peer public tracer. Parent reran the four suffix controls on the shared merged code and verified clean source identity.
- Source handoff is now available for canonical integration, but this merge **does not attach score matmul to the canonical entry**. The canonical boundary remains K AA(2,1), with the previously accepted 2,498,688-byte/131-module bundle; no new score-stage bundle-budget result is claimed. Canonical/DAG/budget attachment remains owned by the integration line.
- Next saved-primal source frontier: original SM division and PM AA(1,3), currently inventoried only. Saved probabilities/logits, the remaining attention/output/residual forward chain and saved-X1317 value reconstruction are not yet closed by this checkpoint. Existing backward readers/DAGs and root dX results are not a substitute for those forward value prerequisites. Whole-model/public completion, an inhabited successful whole-capture execution and Torch/CUDA refinement remain open; renderer flags stay false/uncompiled despite these external exact-source kernel receipts.
- Evidence: `/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/backward-score-matmul-acceptance/`, especially `acceptance.json`, `review/review.json`, `actual1/FreshScoreMatmul-kernel.json`, `actual1/ProjectionFrontierJoint-check.json` and `postmerge-suffix.result.json`. Earlier interrupted/failed worker diagnostics remain historical; final worker closure and these parent gates supersede them. Historical worktrees/object caches remain preserved while receipts refer to them. No push or merge to main.

## Local worktree cleanup and recovery

- Scope approved by the user: TrainVerify and nnScaler; no remote pushes or remote-branch deletions. All 298 initial worktree instances have an explicit disposition in `/home/v-zhouziyu/trainverify-audits/worktree-cleanup/20260913T144750Z/worktrees-checklist.json`.
- TrainVerify: 293 → 10 materialized worktrees; nnScaler: 5 → 1. The only development integration roots are this checkout and `/home/v-zhouziyu/work/nnscaler-internal`. The nine other TrainVerify roots are deliberately retained Git/cache/exact-source/evidence dependencies, not missing feature merges. Removing them safely requires a separate path-binding migration; the main `.lake/build` is part of the live accepted object chain and was not deleted.
- No confirmed missing production capability or proof required importing an older candidate. Exact ancestry, patch equivalence, complete contribution-blob equality and 110 immutable semantic-difference reviews distinguish absorbed improvements from archived experiments. No `merge -s ours`, weakened guard or fake kernel acceptance was used to label history merged.
- Every initial HEAD is recoverable under `refs/heads/archive/cleanup-20260913T144750Z/<original-worktree-basename>`. Retired original worker branch labels are mapped to those refs in `retired-local-branches.json`.
- Dirty staged/unstaged changes and untracked files were separately preserved. Before retiring the remaining private-data trees, all ignored/untracked extras were archived with member verification; regular symlink targets were additionally retained by content, while dependency directories outside the retired set remain in place. See `dirty-backups/`, `retirement-backups/`, `derived-cache-backups/` and their manifests. Restore the committed tree first, then the staged/unstaged patches and extras into an isolated checkout; consult the original-path/target mapping rather than blindly dereferencing archive links.
- Six unique Layernorm parameter research probes remain protected in the main Git/cache tree and in recovery archives; their use of native_decide does not make them accepted production proofs. Historical regression replacements at `aabf5106338c` and `7481367ffb42` remain explicitly unconfirmed; complete HEADs/tests are archived, not discarded or blindly merged.
- The cleanup does not advance the canonical proof boundary or resolve any whole-model/public/Torch obligation. Source remains the already reviewed integrated score-matmul handoff plus canonical middle-exchange boundary. Formal Whole snapshots, trusted captures, current bound sources/objects and the nnScaler wheel/smoke evidence remain preserved.

## Reproduction / receipts

Integration checks, exact source preservation, protected-tree inventory, partial-test checkpoints and final coverage reconciliation are under:

`/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/worktree-consolidation/`

The external test runners pin this checkout, use the existing trusted captures and private caches, and reject staged/working-tree drift. Tests requiring capture or Lean are not counted as passed merely because their optional configuration was absent. Interrupted runs preserve only confirmed completed cases; remaining cases are explicitly enumerated and reconciled against the complete collected test set.
