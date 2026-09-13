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

The QKV partition's 21 changed paths and backward partition's 179 changed paths were compared to their exact committed blobs at the merge candidate. All matched. The partitions overlap; these counts are not additive feature counts.

## Single-owner division

- **Integration/parallel line:** shared authority interfaces, canonical frontier/DAG assembly, source budget and whole-model/public acceptance. It reuses the source-bound forward dependency implementations already supplied by the backward line; it does not start another Q/K/V implementation.
- **Backward/saved-primal line:** continuation required for saved primal reconstruction and gradients. The post-transpose continuation has been handed off through merge `b60e7288`; subsequent saved-primal and gradient work remains with this line.
- Before new implementation fan-out, compare related live worktrees and semantic targets (fullrefs, shapes, axes, parameter binding and frontier order). A backward saved-primal dependency can be the same forward task, despite different channel/branch names.
- Shared file edits have one writer. New workers branch from an agreed integrated commit in isolated worktrees and use private caches. Existing active workers are not forcibly rebased, reset or cleaned.
- This file records the intended coordination boundary. It does not claim another chat has received or acknowledged a reassignment.

## Protected unfinished work and evidence

- `/home/v-zhouziyu/work/trainverify-backward-forward-post-transpose`: preserved development/evidence checkout, clean at `8db687e1`. Its complete committed post-transpose chain is imported through `b60e7288`; no mutable-index copying or reset was used.
- `/home/v-zhouziyu/work/trainverify-backward-matmul-next/.hermes/`: private generated source, raw-census, kernel and review receipts; retained at their original paths.
- Existing forward/backward proof, review and accepted-cache worktrees remain available while those receipts or running owners refer to them. Their retention does not make them a second integration authority.
- Only the three never-launched, unchanged `trainverify-qkv-{q,kv,authority}-copilot` worktrees were removed, without force.

## Acceptance boundaries

- The old backward handoff's statement about the sequence-alias bundle exceeding 2,500,000 bytes describes its earlier checkpoint. The forward baseline already resolved that issue with v4; do not repeat the codec work.
- The accepted **alias-stage** bundle was 2,489,883 bytes. That is not a byte-size result for a newly assembled QKV/backward bundle.
- Source consolidation, Python/public-entry regression and focused helper kernel checks do not by themselves establish canonical whole-model assembly, a successful whole-capture run, saved-X1317 reconstruction or Torch refinement.
- QKV helper/frontier facts remain complete conditional contracts with their original common-run and initial-parameter hypotheses. No premise or theorem was weakened by this merge.
- The post-transpose stage, including the retained-fact fix, is now inside the canonical attachment boundary (see its checkpoint below). K middle exchange is imported source but not yet canonically attached. Neither checkpoint implies whole-model acceptance. The integration line owns canonical assembly/acceptance; the backward owner owns saved-primal continuation. Coordinate interface changes before overlapping work.
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
- K middle-exchange source/tests remain byte-preserved but are **not yet canonically attached**. The next integration slice may attach that handed-off stage; Q/K matmul and later saved-primal operator development remain with the backward line.
- Evidence: `/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/canonical-post-transpose/`, especially `final-review/review.json` and `postmerge/gate.json`. This is conditional canonical frontier acceptance, not whole-model/public completion, saved-X1317 reconstruction or Torch refinement. No push to main.

## Reproduction / receipts

Integration checks, exact source preservation, protected-tree inventory, partial-test checkpoints and final coverage reconciliation are under:

`/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/worktree-consolidation/`

The external test runners pin this checkout, use the existing trusted captures and private caches, and reject staged/working-tree drift. Tests requiring capture or Lean are not counted as passed merely because their optional configuration was absent. Interrupted runs preserve only confirmed completed cases; remaining cases are explicitly enumerated and reconciled against the complete collected test set.
