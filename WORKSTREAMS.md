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
- The post-transpose successor stage is now inside the imported source boundary, including the retained-fact fix. This is not canonical DAG wiring or whole-model acceptance. The integration line owns eventual canonical assembly/acceptance; the backward owner owns saved-primal continuation. Coordinate interface changes before starting overlapping work.
- At the user's request, no new implementation fan-out starts until this committed handoff and integration verification are complete and the integration worktree is clean.

## Post-transpose handoff verification

- Source handoff: `cf53bd9a` plus `8db687e1`, merged by `b60e7288`. Exact two-file blobs match the source-reviewed fix.
- Integrated regression: **219 passed, zero failures/errors/skips**; complete collected node IDs were partitioned into three disjoint 73-case batches, with persisted JUnit and result reconciliation.
- Fresh integrated saved-source replay and raw census: **9 reads, 4 complete unit relations, 8 frontier rows, 2 deferred Q rows, 2 residual carries**.
- Exact source/object/dependency closure and all-eight mixed-layout joint passed; V retains every-replica equality rather than a fabricated gather-axis contract. All 13 new declarations use only the standard three axioms. This remains local conditional proof evidence, not canonical whole-model acceptance.
- Private evidence: `/home/v-zhouziyu/work/trainverify-backward-matmul-next/.hermes/forward-value-continuation/post-transpose-integrated/` and sibling `post-transpose-integrated-tests/`.
- Both old worker source and shared integration must be clean before subsequent isolated implementation starts. Shared canonical/DAG files remain exclusively owned by the parallel line.

## Reproduction / receipts

Integration checks, exact source preservation, protected-tree inventory, partial-test checkpoints and final coverage reconciliation are under:

`/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/worktree-consolidation/`

The external test runners pin this checkout, use the existing trusted captures and private caches, and reject staged/working-tree drift. Tests requiring capture or Lean are not counted as passed merely because their optional configuration was absent. Interrupted runs preserve only confirmed completed cases; remaining cases are explicitly enumerated and reconciled against the complete collected test set.
